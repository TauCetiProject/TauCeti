/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Chevalley.Basic
public import Mathlib.Algebra.Lie.Solvable
public import TauCeti.Algebra.Lie.Prod
public import TauCeti.Algebra.Lie.Solvable.Basic
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Balanced.Finite
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Basic
import TauCeti.Algebra.Lie.BaseChange.MaxTrivSubmodule
import TauCeti.LinearAlgebra.TensorProduct.Submodule
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# The central and derived parts of a full Chevalley Lie algebra

Scalar extension retains the full cocharacter lattice of the integral Chevalley algebra.
Its derived algebra is spanned by all root vectors and the coroot Cartan vectors when two
is invertible. In characteristic zero the remaining toral directions form its center.
No splitting of the integral cocharacter lattice is required.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§8 and 25.
* J. C. Jantzen, *Representations of Algebraic Groups*, Part II, Chapter 1.

The scalar-extension coordinates and the generator calculation of the derived ideal follow
`Matrix.FullShellLieAlgebra.baseChangeEquiv` and the proofs in
`TauCeti.Algebra.Lie.NormTwoShell.FullCartan.Derived`.
-/

public section

open scoped TensorProduct
open Module Set

namespace RootPairing.ChevalleyLieAlgebra

noncomputable section

variable {ι X Y : Type*} [Finite ι] [AddCommGroup X] [AddCommGroup Y]
  {P : RootPairing ι ℤ X Y} (c : P.ChevalleyConstants)
  (A : Type*) [CommRing A]

open Classical in
/-- Coordinates of the scalar extension, with the full toral module as first factor. -/
def baseChangeEquiv : A ⊗[ℤ] ChevalleyLieAlgebra c ≃ₗ[A]
    (A ⊗[ℤ] Y) × (ι →₀ A) :=
  LinearEquiv.baseChange ℤ A _ _ (equivProd c) ≪≫ₗ
    TensorProduct.prodRight ℤ A A Y (ι →₀ ℤ) ≪≫ₗ
    (LinearEquiv.refl A _).prodCongr (TensorProduct.finsuppScalarRight ℤ A A ι)

@[simp] theorem baseChangeEquiv_tmul_fst (a : A) (x : ChevalleyLieAlgebra c) :
    (baseChangeEquiv c A (a ⊗ₜ[ℤ] x)).1 = a ⊗ₜ[ℤ] (equivProd c x).1 := by
  simp [baseChangeEquiv]

@[simp] theorem baseChangeEquiv_tmul_snd_apply (a : A) (x : ChevalleyLieAlgebra c) (i : ι) :
    (baseChangeEquiv c A (a ⊗ₜ[ℤ] x)).2 i = (equivProd c x).2 i • a := by
  simp [baseChangeEquiv]

@[simp] theorem baseChangeEquiv_cartan (y : A ⊗[ℤ] Y) :
    baseChangeEquiv c A ((cartan c).baseChange A y) = (y, 0) := by
  induction y using TensorProduct.inductionOn with
  | tmul a y => apply Prod.ext <;> simp [Finsupp.ext_iff]
  | add y z hy hz => simp [hy, hz]

@[simp] theorem baseChangeEquiv_tmul_root (a : A) (i : ι) :
    baseChangeEquiv c A (a ⊗ₜ[ℤ] root c i) = (0, Finsupp.single i a) := by
  classical
  apply Prod.ext
  · simp
  · ext j; by_cases h : i = j <;> simp [h]

/-- Reconstruct an element from its toral coordinate and its root coefficients. -/
theorem baseChangeEquiv_symm_apply (y : A ⊗[ℤ] Y) (f : ι →₀ A) :
    (baseChangeEquiv c A).symm (y, f) =
      (cartan c).baseChange A y + f.sum (fun i a ↦ a ⊗ₜ[ℤ] root c i) := by
  apply (baseChangeEquiv c A).injective
  simp only [LinearEquiv.apply_symm_apply, map_add, baseChangeEquiv_cartan, map_finsuppSum,
    baseChangeEquiv_tmul_root]
  apply Prod.ext
  · simp [Finsupp.sum, Prod.fst_sum]
  · simpa only [Finsupp.sum, Prod.snd_add, Prod.snd_sum, Prod.snd_zero, zero_add] using
      (Finsupp.sum_single f).symm

/-- Every bracket has toral coordinate in the integral span of the coroots. -/
theorem lie_mem_span_cartan_coroot_root (x y : ChevalleyLieAlgebra c) :
    ⁅x, y⁆ ∈ Submodule.span ℤ (range (fun i ↦ cartan c (P.coroot i)) ∪ range (root c)) := by
  classical
  let S := Submodule.span ℤ (range (fun i ↦ cartan c (P.coroot i)) ∪ range (root c))
  have hr (i : ι) : root c i ∈ S := Submodule.subset_span (Or.inr (mem_range_self i))
  have hb (i j : ι) : rootBracket c i j ∈ S := by
    by_cases h : P.root i + P.root j = 0
    · rw [rootBracket_of_add_eq_zero c h]
      exact Submodule.subset_span (Or.inl (mem_range_self i))
    · by_cases hm : P.root i + P.root j ∈ range P.root
      · obtain ⟨k, hk⟩ := hm
        rw [rootBracket_of_root_eq_add c hk]
        exact S.smul_mem _ (hr k)
      · rw [rootBracket_of_notMem_of_add_ne_zero c hm h]
        exact S.zero_mem
  have h : (bracketBilin c).compr₂ S.mkQ = 0 := by
    refine linearMap_ext (fun y ↦ linearMap_ext (fun z ↦ ?_) fun j ↦ ?_)
      fun i ↦ linearMap_ext (fun z ↦ ?_) fun j ↦ ?_ <;>
      simp only [LinearMap.compr₂_apply, bracketBilin_apply_apply, LinearMap.zero_apply]
    · simp
    · exact (Submodule.Quotient.mk_eq_zero S).mpr (by
        simpa only [cartan_lie_root] using S.smul_mem _ (hr j))
    · exact (Submodule.Quotient.mk_eq_zero S).mpr (by
        simpa only [root_lie_cartan] using S.neg_mem (S.smul_mem _ (hr i)))
    · exact (Submodule.Quotient.mk_eq_zero S).mpr (by
        simpa only [root_lie_root] using hb i j)
  exact (Submodule.Quotient.mk_eq_zero S).mp (congr($h x y))

/-- Every coroot Cartan vector belongs to the derived algebra after any scalar extension. -/
theorem tmul_cartan_coroot_mem_derivedSeries_one (i : ι) :
    (1 : A) ⊗ₜ[ℤ] cartan c (P.coroot i) ∈
      LieAlgebra.derivedSeries A (A ⊗[ℤ] ChevalleyLieAlgebra c) 1 := by
  have h := LieSubmodule.lie_mem_lie
    (I := (⊤ : LieIdeal A (A ⊗[ℤ] ChevalleyLieAlgebra c)))
    (N := (⊤ : LieIdeal A (A ⊗[ℤ] ChevalleyLieAlgebra c)))
    (x := (1 : A) ⊗ₜ[ℤ] root c i) (m := (1 : A) ⊗ₜ[ℤ] root c (P.reflectionPerm i i))
    (by trivial) (by trivial)
  simpa using h

/-- With two invertible, every root vector is a commutator with its own coroot. -/
theorem tmul_root_mem_derivedSeries_one [Invertible (2 : A)] (i : ι) :
    (1 : A) ⊗ₜ[ℤ] root c i ∈
      LieAlgebra.derivedSeries A (A ⊗[ℤ] ChevalleyLieAlgebra c) 1 := by
  have h := LieSubmodule.lie_mem_lie
    (I := (⊤ : LieIdeal A (A ⊗[ℤ] ChevalleyLieAlgebra c)))
    (N := (⊤ : LieIdeal A (A ⊗[ℤ] ChevalleyLieAlgebra c)))
    (x := (⅟ (2 : A)) ⊗ₜ[ℤ] cartan c (P.coroot i)) (m := (1 : A) ⊗ₜ[ℤ] root c i)
    (by trivial) (by trivial)
  have heq : ⁅(⅟ (2 : A)) ⊗ₜ[ℤ] cartan c (P.coroot i), (1 : A) ⊗ₜ[ℤ] root c i⁆ =
      (1 : A) ⊗ₜ[ℤ] root c i := by
    simp only [LieAlgebra.ExtendScalars.bracket_tmul, mul_one, cartan_lie_root,
      P.root_coroot_eq_pairing, P.pairing_same, two_smul ℤ,
      TensorProduct.tmul_add, ← TensorProduct.add_tmul]
    congr 1
    simpa only [two_mul] using mul_invOf_self (2 : A)
  rwa [heq] at h

/-- Over any ring with two invertible, the derived algebra is spanned by the coroot Cartan
vectors and all root lines. -/
theorem derivedSeries_one_eq_span [Invertible (2 : A)] :
    (LieAlgebra.derivedSeries A (A ⊗[ℤ] ChevalleyLieAlgebra c) 1).toSubmodule =
      Submodule.span A (range (fun i ↦ (1 : A) ⊗ₜ[ℤ] cartan c (P.coroot i)) ∪
        range (fun i ↦ (1 : A) ⊗ₜ[ℤ] root c i)) := by
  apply le_antisymm
  · have h : (LieAlgebra.derivedSeries ℤ (ChevalleyLieAlgebra c) 1).toSubmodule ≤
        Submodule.span ℤ (range (fun i ↦ cartan c (P.coroot i)) ∪ range (root c)) := by
      rw [← LieIdeal.toLieSubalgebra_toSubmodule, LieAlgebra.coe_derivedSeries_one_eq]
      exact Submodule.span_le.mpr fun _ ⟨x, y, hxy⟩ ↦ hxy ▸
        lie_mem_span_cartan_coroot_root c x y
    rw [LieAlgebra.derivedSeries_baseChange, LieSubmodule.coe_baseChange]
    refine (Submodule.baseChange_mono A h).trans ?_
    simp only [Submodule.baseChange_span, image_union, ← range_comp, Function.comp_def]
    exact le_rfl
  · refine Submodule.span_le.mpr ?_
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact tmul_cartan_coroot_mem_derivedSeries_one c A i
    · exact tmul_root_mem_derivedSeries_one c A i

variable {A} in
/-- Linear maps on a scalar-extended Chevalley algebra are determined by the integral Cartan
generators and root vectors. -/
theorem baseChange_linearMap_ext {N : Type*} [AddCommGroup N] [Module A N]
    {f g : A ⊗[ℤ] ChevalleyLieAlgebra c →ₗ[A] N}
    (hc : ∀ y, f (1 ⊗ₜ[ℤ] cartan c y) = g (1 ⊗ₜ[ℤ] cartan c y))
    (hr : ∀ i, f (1 ⊗ₜ[ℤ] root c i) = g (1 ⊗ₜ[ℤ] root c i)) : f = g := by
  have h : (f.restrictScalars ℤ).comp (TensorProduct.mk ℤ A _ 1) =
      (g.restrictScalars ℤ).comp (TensorProduct.mk ℤ A _ 1) := linearMap_ext hc hr
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  have hx : f (1 ⊗ₜ[ℤ] x) = g (1 ⊗ₜ[ℤ] x) := LinearMap.congr_fun h x
  simpa only [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    using congrArg (a • ·) hx

variable [Free ℤ Y] [Module.Finite ℤ Y]

/-- In coordinates, the derived ideal has exactly the coroot span as its toral part; all root
coordinates are unrestricted. -/
theorem mem_derivedSeries_one_iff [FaithfulSMul ℤ A] [Invertible (2 : A)]
    (x : A ⊗[ℤ] ChevalleyLieAlgebra c) :
    x ∈ LieAlgebra.derivedSeries A (A ⊗[ℤ] ChevalleyLieAlgebra c) 1 ↔
      (baseChangeEquiv c A x).1 ∈ (P.baseChange A).corootSpan A := by
  let D := (LieAlgebra.derivedSeries A (A ⊗[ℤ] ChevalleyLieAlgebra c) 1).toSubmodule
  let T := (P.baseChange A).corootSpan A
  constructor
  · intro hx
    have h : D ≤ T.comap ((LinearMap.fst A _ _).comp (baseChangeEquiv c A).toLinearMap) := by
      dsimp only [D]
      rw [derivedSeries_one_eq_span]
      refine Submodule.span_le.mpr ?_
      rintro z (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · simpa [T] using Submodule.subset_span (mem_range_self (f := (P.baseChange A).coroot) i)
      · simp
    exact h hx
  · intro hx
    have hcartan (y : A ⊗[ℤ] Y) (hy : y ∈ T) : (cartan c).baseChange A y ∈ D := by
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        simpa [D] using tmul_cartan_coroot_mem_derivedSeries_one c A i
      | zero => simp
      | add y z _ _ hy hz => simpa using D.add_mem hy hz
      | smul a y _ hy => simpa using D.smul_mem a hy
    rw [← (baseChangeEquiv c A).symm_apply_apply x, baseChangeEquiv_symm_apply]
    apply D.add_mem (hcartan _ hx)
    exact D.sum_mem fun i _ ↦ by
      simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
        D.smul_mem ((baseChangeEquiv c A x).2 i)
        (tmul_root_mem_derivedSeries_one c A i)

omit [Free ℤ Y] [Module.Finite ℤ Y] in
@[simp] theorem baseChange_cartan_lie_cartan (y z : A ⊗[ℤ] Y) :
    ⁅(cartan c).baseChange A y, (cartan c).baseChange A z⁆ = 0 := by
  induction y using TensorProduct.inductionOn with
  | tmul a y =>
    induction z using TensorProduct.inductionOn with
    | tmul b z => simp
    | add z w hz hw => rw [map_add, LieRing.lie_add, hz, hw, add_zero]
  | add y w hy hw => rw [map_add, LieRing.add_lie, hy, hw, add_zero]

/-- The scalar-extended Cartan action is evaluation of the scalar-extended root. -/
@[simp] theorem baseChange_cartan_lie_root [FaithfulSMul ℤ A]
    (y : A ⊗[ℤ] Y) (a : A) (i : ι) :
    ⁅(cartan c).baseChange A y, a ⊗ₜ[ℤ] root c i⁆ =
      ((P.baseChange A).root' i y * a) ⊗ₜ[ℤ] root c i := by
  induction y using TensorProduct.inductionOn with
  | tmul b y =>
    simp [TensorProduct.tmul_smul, TensorProduct.smul_tmul', mul_assoc, mul_left_comm]
  | add y z hy hz =>
    simp [hy, hz, add_mul, TensorProduct.add_tmul]

/-- A scalar-extended toral vector is central exactly when all roots annihilate it. -/
theorem baseChange_cartan_mem_center_iff [FaithfulSMul ℤ A] (y : A ⊗[ℤ] Y) :
    (cartan c).baseChange A y ∈ LieAlgebra.center A (A ⊗[ℤ] ChevalleyLieAlgebra c) ↔
      y ∈ (P.baseChange A).flip.corootKer := by
  rw [RootPairing.mem_corootKer]
  constructor
  · intro h i
    have hi := congrArg (fun z ↦ (baseChangeEquiv c A z).2 i) (h (1 ⊗ₜ[ℤ] root c i))
    rw [← lie_skew, baseChange_cartan_lie_root] at hi
    have hi' : (P.baseChange A).root' i y = 0 := by simpa using hi
    exact hi'
  · intro h
    have hz : LieAlgebra.ad A (A ⊗[ℤ] ChevalleyLieAlgebra c)
        ((cartan c).baseChange A y) = 0 := by
      apply baseChange_linearMap_ext c
      · intro z
        simpa using baseChange_cartan_lie_cartan c A y ((1 : A) ⊗ₜ[ℤ] z)
      · intro i
        simpa using baseChange_cartan_lie_root c A y 1 i |>.trans (by
          have hi : (P.baseChange A).root' i y = 0 := h i
          rw [hi]
          simp)
    intro x
    rw [← lie_skew]
    exact neg_eq_zero.mpr (LinearMap.congr_fun hz x)

variable (K : Type*) [Field K] [CharZero K]

/-- The center consists of the common root kernel in the toral coordinate and zero root
coordinates. This retains all central directions of the full cocharacter lattice. -/
theorem mem_center_baseChange_iff (x : K ⊗[ℤ] ChevalleyLieAlgebra c) :
    x ∈ LieAlgebra.center K (K ⊗[ℤ] ChevalleyLieAlgebra c) ↔
      (baseChangeEquiv c K x).2 = 0 ∧
        (baseChangeEquiv c K x).1 ∈ (P.baseChange K).flip.corootKer := by
  have hcoord (y : Y) (i : ι) :
      (baseChangeEquiv c K ⁅(1 : K) ⊗ₜ[ℤ] cartan c y, x⁆).2 i =
        (P.toLinearMap (P.root i) y : K) * (baseChangeEquiv c K x).2 i := by
    induction x using TensorProduct.inductionOn with
    | tmul a x => simp [equivProd_cartan_lie_snd, mul_comm, mul_left_comm]
    | add x z hx hz => simp [LieRing.lie_add, hx, hz, mul_add]
  constructor
  · intro hx
    have hr : (baseChangeEquiv c K x).2 = 0 := by
      ext i
      have hi := hcoord (P.coroot i) i
      rw [hx, map_zero] at hi
      simpa [P.root_coroot_eq_pairing, P.pairing_same] using hi.symm
    have heq : x = (cartan c).baseChange K (baseChangeEquiv c K x).1 :=
      (baseChangeEquiv c K).injective (by rw [baseChangeEquiv_cartan]; exact Prod.ext rfl hr)
    exact ⟨hr, (baseChange_cartan_mem_center_iff c K _).mp (heq ▸ hx)⟩
  · rintro ⟨hr, hy⟩
    have heq : x = (cartan c).baseChange K (baseChangeEquiv c K x).1 :=
      (baseChangeEquiv c K).injective (by rw [baseChangeEquiv_cartan]; exact Prod.ext rfl hr)
    rw [heq]
    exact (baseChange_cartan_mem_center_iff c K _).mpr hy

omit [Free ℤ Y] in
/-- For flat coefficients, the integral center formula extends to the scalar-extended toral
module. In particular rationalization preserves the entire integral central lattice. -/
theorem center_baseChange_eq_map [Module.Flat ℤ A] :
    (LieAlgebra.center A (A ⊗[ℤ] ChevalleyLieAlgebra c)).toSubmodule =
      (((⨅ i : ι, LinearMap.ker (P.root' i)).baseChange A).map ((cartan c).baseChange A)) := by
  let : Module.Finite ℤ (ChevalleyLieAlgebra c) := Module.Finite.equiv (equivProd c).symm
  have h := congrArg LieSubmodule.toSubmodule
    (LieModule.maxTrivSubmodule_baseChange ℤ A (ChevalleyLieAlgebra c) (ChevalleyLieAlgebra c))
  calc
    _ = (LieAlgebra.center ℤ (ChevalleyLieAlgebra c)).toSubmodule.baseChange A := h
    _ = _ := by rw [center_eq_map_iInf_ker, Submodule.baseChange_map]

/-- Over a characteristic-zero field the center and derived ideal of the full Chevalley algebra
are complementary. The complement is obtained only after extending the cocharacter lattice. -/
theorem isCompl_center_derivedSeries_one :
    IsCompl (LieAlgebra.center K (K ⊗[ℤ] ChevalleyLieAlgebra c))
      (LieAlgebra.derivedSeries K (K ⊗[ℤ] ChevalleyLieAlgebra c) 1) := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  have h := (P.baseChange K).flip.isCompl_rootSpan_corootKer
  apply LieSubmodule.isCompl_toSubmodule.mp
  rw [isCompl_iff]
  constructor
  · apply Submodule.disjoint_def.mpr
    intro x hz hd
    obtain ⟨hr, hk⟩ := (mem_center_baseChange_iff c K x).mp hz
    have hs := (mem_derivedSeries_one_iff c K x).mp hd
    have ht := Submodule.disjoint_def.mp h.disjoint _ hs hk
    apply (baseChangeEquiv c K).injective
    rw [map_zero]
    exact Prod.ext ht hr
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    obtain ⟨p, hp, _⟩ := Submodule.existsUnique_add_of_isCompl_prod h
      (baseChangeEquiv c K x).1
    let z := (cartan c).baseChange K (p.2 : K ⊗[ℤ] Y)
    apply Submodule.mem_sup.mpr
    refine ⟨z, (baseChange_cartan_mem_center_iff c K _).mpr p.2.property, x - z, ?_,
      add_sub_cancel _ _⟩
    apply (mem_derivedSeries_one_iff c K _).mpr
    have heq : (baseChangeEquiv c K (x - z)).1 = p.1 := by
      simp only [map_sub, z, baseChangeEquiv_cartan, Prod.fst_sub]
      rw [← hp, add_sub_cancel_right]
    rw [heq]
    exact p.1.property

/-- Addition identifies the product of the center and derived ideal with the full scalar-extended
Chevalley Lie algebra, retaining every central toral direction. -/
def centerDerivedEquiv :
    (LieAlgebra.center K (K ⊗[ℤ] ChevalleyLieAlgebra c) ×
      LieAlgebra.derivedSeries K (K ⊗[ℤ] ChevalleyLieAlgebra c) 1) ≃ₗ⁅K⁆
      K ⊗[ℤ] ChevalleyLieAlgebra c :=
  LieIdeal.prodEquivOfIsCompl _ _ (isCompl_center_derivedSeries_one c K)

@[simp] theorem centerDerivedEquiv_apply
    (p : LieAlgebra.center K (K ⊗[ℤ] ChevalleyLieAlgebra c) ×
      LieAlgebra.derivedSeries K (K ⊗[ℤ] ChevalleyLieAlgebra c) 1) :
    centerDerivedEquiv c K p = (p.1 : K ⊗[ℤ] ChevalleyLieAlgebra c) + p.2 :=
  LieIdeal.prodEquivOfIsCompl_apply _ _ _ p

@[simp] theorem centerDerivedEquiv_symm_center
    (z : LieAlgebra.center K (K ⊗[ℤ] ChevalleyLieAlgebra c)) :
    (centerDerivedEquiv c K).symm z = (z, 0) :=
  LieIdeal.prodEquivOfIsCompl_symm_apply_left _ _ _ z

@[simp] theorem centerDerivedEquiv_symm_derivedSeries
    (d : LieAlgebra.derivedSeries K (K ⊗[ℤ] ChevalleyLieAlgebra c) 1) :
    (centerDerivedEquiv c K).symm d = (0, d) :=
  LieIdeal.prodEquivOfIsCompl_symm_apply_right _ _ _ d

/-- Every Lie algebra automorphism acts separately on the two factors of the central/derived
decomposition. No compatibility with the chosen root vectors is required. -/
theorem centerDerivedEquiv_symm_map
    (e : (K ⊗[ℤ] ChevalleyLieAlgebra c) ≃ₗ⁅K⁆ (K ⊗[ℤ] ChevalleyLieAlgebra c))
    (x : K ⊗[ℤ] ChevalleyLieAlgebra c) :
    (centerDerivedEquiv c K).symm (e x) =
      (e.toLieHom.restrictIdeal
        (fun _ hz ↦ LieHom.map_center_le_center _ e.surjective (LieIdeal.mem_map hz))
        ((centerDerivedEquiv c K).symm x).1,
       e.toLieHom.restrictIdeal (fun _ hd ↦ e.toLieHom.map_mem_derivedSeries 1 hd)
        ((centerDerivedEquiv c K).symm x).2) :=
  LieIdeal.prodEquivOfIsCompl_symm_map _ _ _ _ _ _ _ x

end

end RootPairing.ChevalleyLieAlgebra
