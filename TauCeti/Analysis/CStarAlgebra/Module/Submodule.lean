/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import TauCeti.Analysis.CStarAlgebra.Ideal
public import TauCeti.Analysis.CStarAlgebra.Module.Self

/-!
# Submodules of Hilbert C⋆-modules and closed right ideals

A Hilbert C⋆-submodule of a (pre-)Hilbert C⋆-module `E` over a possibly nonunital C⋆-algebra `A`
is a complex linear subspace `F ⊆ E` that is stable under the coefficient action `a • x` of `A`.
Because `A` need not have a unit, Mathlib's `Submodule A E` is not available in general;
`TauCeti.CStarSubmodule A E` bundles a `Submodule ℂ E` together with stability under `SMul A E`.
For a right Hilbert `B`-module (`CStarModule Bᵐᵒᵖ E`), take `A = Bᵐᵒᵖ`.

Every `F : CStarSubmodule A E` inherits `NormedAddCommGroup F`, `NormedSpace ℂ F`, `SMul A F`,
and `CStarModule A F`, and is complete whenever `E` is complete and `F` is closed. The subtype
inclusions `F.subtype`, `F.subtypeₗᵢ`, and `F.subtypeL` preserve both the `A`-valued inner product
and the `A`-action.

In the right self-module `CStarModule Aᵐᵒᵖ A`, `CStarSubmodule Aᵐᵒᵖ A` consists of complex-linear
right ideals of `A`. Every closed right additive subgroup of a (possibly nonunital) C⋆-algebra `A`
is automatically `ℂ`-linear via an approximate unit (`CStarSubmodule.ofClosedRightAddSubgroup`),
yielding a closed right Hilbert `A`-submodule of `A`; closed two-sided ideals
(`TwoSidedIdeal.toCStarSubmodule`), right ideals of unital algebras (`Ideal.toCStarSubmodule`),
and submodules over unital coefficient algebras (`Submodule.toCStarSubmodule`) embed canonically
as well.

## Main declarations

* `TauCeti.CStarSubmodule`: complex submodules stable under the coefficient action `SMul A E`,
  with `CompleteLattice`, `SMul A F`, `CStarModule A F`, and `topologicalClosure`.
* `TauCeti.CStarSubmodule.ofRightIdeal`, `TauCeti.CStarSubmodule.ofClosedRightAddSubgroup`,
  `TauCeti.CStarSubmodule.rightFixedSubmodule`, `TwoSidedIdeal.toCStarSubmodule`,
  `Ideal.toCStarSubmodule`, `Submodule.toCStarSubmodule`: right ideals of `A` as submodules
  of the right self-module `CStarModule Aᵐᵒᵖ A`, and unital submodules as `CStarSubmodule`s.

## References

* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Chapter 2.
* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1.
-/

public section

open MulOpposite Filter Topology

namespace TauCeti

/-- A C⋆-submodule of a module `E` over a possibly nonunital algebra `A`: a complex submodule
of `E` closed under the coefficient action `SMul A E`. For right Hilbert `B`-modules, take
`A = Bᵐᵒᵖ`. -/
structure CStarSubmodule (A E : Type*) [AddCommGroup E] [Module ℂ E] [SMul A E]
    extends Submodule ℂ E where
  /-- Stability under the coefficient action `SMul A E`. -/
  smul_mem_coeff' : ∀ (a : A) {x : E}, x ∈ carrier → a • x ∈ carrier

attribute [coe] CStarSubmodule.toSubmodule

namespace CStarSubmodule

section Basic

variable {A E : Type*} [AddCommGroup E] [Module ℂ E] [SMul A E]

instance : SetLike (CStarSubmodule A E) E where
  coe F := F.carrier
  coe_injective F G h := by
    cases F
    cases G
    congr
    exact SetLike.coe_injective h

instance : PartialOrder (CStarSubmodule A E) := .ofSetLike (CStarSubmodule A E)

instance : AddSubgroupClass (CStarSubmodule A E) E where
  add_mem {F} _ _ := F.add_mem'
  zero_mem F := F.zero_mem'
  neg_mem {F} _ hx := F.toSubmodule.neg_mem hx

instance instSMulMemClass : SMulMemClass (CStarSubmodule A E) ℂ E where
  smul_mem {F} c _ hx := F.smul_mem' c hx

instance (priority := mid) instCoeOutSubmodule :
    CoeOut (CStarSubmodule A E) (Submodule ℂ E) :=
  ⟨toSubmodule⟩

instance : CanLift (Submodule ℂ E) (CStarSubmodule A E) toSubmodule
    (fun F ↦ ∀ (a : A) {x : E}, x ∈ F → a • x ∈ F) where
  prf F hF := ⟨⟨F, hF⟩, rfl⟩

/-- Two C⋆-submodules with the same elements are equal. -/
@[ext]
theorem ext {F G : CStarSubmodule A E} (h : ∀ x, x ∈ F ↔ x ∈ G) : F = G :=
  SetLike.ext h

theorem toSubmodule_injective :
    Function.Injective (toSubmodule : CStarSubmodule A E → Submodule ℂ E) := fun F G h ↦ by
  cases F
  cases G
  congr

@[simp]
theorem toSubmodule_inj {F G : CStarSubmodule A E} :
    F.toSubmodule = G.toSubmodule ↔ F = G :=
  toSubmodule_injective.eq_iff

@[simp]
theorem toSubmodule_le_toSubmodule {F G : CStarSubmodule A E} :
    F.toSubmodule ≤ G.toSubmodule ↔ F ≤ G :=
  (Iff.rfl)

@[simp]
theorem mem_toSubmodule {F : CStarSubmodule A E} {x : E} :
    x ∈ F.toSubmodule ↔ x ∈ F :=
  (Iff.rfl)

@[norm_cast]
theorem coe_toSubmodule (F : CStarSubmodule A E) :
    ((F.toSubmodule : Submodule ℂ E) : Set E) = F :=
  (rfl)

@[simp]
theorem mem_mk {F : Submodule ℂ E} {hF : ∀ (a : A) {x : E}, x ∈ F → a • x ∈ F} {x : E} :
    x ∈ (⟨F, hF⟩ : CStarSubmodule A E) ↔ x ∈ F :=
  (Iff.rfl)

@[simp]
theorem toSubmodule_mk (F : Submodule ℂ E) (hF : ∀ (a : A) {x : E}, x ∈ F → a • x ∈ F) :
    (⟨F, hF⟩ : CStarSubmodule A E).toSubmodule = F :=
  (rfl)

/-- A C⋆-submodule is closed under the coefficient action `a • x`. -/
theorem smul_mem_coeff (F : CStarSubmodule A E) (a : A) {x : E} (hx : x ∈ F) : a • x ∈ F :=
  F.smul_mem_coeff' a hx

/-- In a right C⋆-submodule (`A = Bᵐᵒᵖ`), right multiplication by `b : B` preserves membership. -/
theorem op_smul_mem {B : Type*} [SMul Bᵐᵒᵖ E] (F : CStarSubmodule Bᵐᵒᵖ E) (b : B) {x : E}
    (hx : x ∈ F) : op b • x ∈ F :=
  F.smul_mem_coeff (op b) hx

/-- A C⋆-submodule inherits the coefficient action `SMul A F`. Lower priority than `SetLike.smul`
so that when `A = ℂ`, the standard complex scalar action is preferred (and both are definitionally
equal). -/
instance (priority := 40) instSMulCoeff (F : CStarSubmodule A E) : SMul A F where
  smul a x := ⟨a • x.val, F.smul_mem_coeff' a x.property⟩

@[simp, norm_cast]
theorem coe_smul_coeff {F : CStarSubmodule A E} (a : A) (x : F) :
    ((a • x : F) : E) = a • (x : E) :=
  (rfl)

@[simp]
theorem mk_eq_zero {F : CStarSubmodule A E} {x : E} (hx : x ∈ F) :
    (⟨x, hx⟩ : F) = 0 ↔ x = 0 :=
  Subtype.ext_iff

/-- The subtype inclusion `F →ₗ[ℂ] E` of a C⋆-submodule. -/
def subtype (F : CStarSubmodule A E) : F →ₗ[ℂ] E :=
  F.toSubmodule.subtype

@[simp]
theorem subtype_apply (F : CStarSubmodule A E) (x : F) : F.subtype x = (x : E) :=
  (rfl)

theorem subtype_injective (F : CStarSubmodule A E) : Function.Injective F.subtype :=
  Subtype.coe_injective

@[simp]
theorem range_subtype (F : CStarSubmodule A E) : LinearMap.range F.subtype = F.toSubmodule :=
  F.toSubmodule.range_subtype

theorem subtype_smul_coeff (F : CStarSubmodule A E) (a : A) (x : F) :
    F.subtype (a • x) = a • F.subtype x :=
  (rfl)

end Basic

/-! ### Complete lattice structure -/

section Lattice

variable {A E : Type*} [AddCommGroup E] [Module ℂ E] [SMul A E]

instance : Top (CStarSubmodule A E) where
  top :=
    { toSubmodule := ⊤
      smul_mem_coeff' := fun _ _ _ ↦ trivial }

instance : Min (CStarSubmodule A E) where
  min F G :=
    { toSubmodule := F.toSubmodule ⊓ G.toSubmodule
      smul_mem_coeff' := fun a _ hx ↦ ⟨F.smul_mem_coeff a hx.1, G.smul_mem_coeff a hx.2⟩ }

instance : InfSet (CStarSubmodule A E) where
  sInf S :=
    { toSubmodule := sInf (toSubmodule '' S)
      smul_mem_coeff' := fun a x hx ↦ by
        refine Submodule.mem_sInf.mpr ?_
        rintro _ ⟨F, hF, rfl⟩
        exact F.smul_mem_coeff a (Submodule.mem_sInf.mp hx F.toSubmodule ⟨F, hF, rfl⟩) }

@[simp]
theorem toSubmodule_top : (⊤ : CStarSubmodule A E).toSubmodule = ⊤ :=
  (rfl)

@[simp]
theorem coe_top : ((⊤ : CStarSubmodule A E) : Set E) = Set.univ :=
  (rfl)

@[simp]
theorem mem_top (x : E) : x ∈ (⊤ : CStarSubmodule A E) :=
  trivial

@[simp]
theorem toSubmodule_inf (F G : CStarSubmodule A E) :
    (F ⊓ G).toSubmodule = F.toSubmodule ⊓ G.toSubmodule :=
  (rfl)

@[simp]
theorem coe_inf (F G : CStarSubmodule A E) :
    ((F ⊓ G : CStarSubmodule A E) : Set E) = (F : Set E) ∩ (G : Set E) :=
  (rfl)

@[simp]
theorem mem_inf {F G : CStarSubmodule A E} {x : E} : x ∈ F ⊓ G ↔ x ∈ F ∧ x ∈ G :=
  (Iff.rfl)

@[simp]
theorem toSubmodule_sInf (S : Set (CStarSubmodule A E)) :
    (sInf S).toSubmodule = sInf (toSubmodule '' S) :=
  (rfl)

@[simp]
theorem mem_sInf {S : Set (CStarSubmodule A E)} {x : E} : x ∈ sInf S ↔ ∀ F ∈ S, x ∈ F := by
  simp [← mem_toSubmodule]

instance : CompleteLattice (CStarSubmodule A E) :=
  { completeLatticeOfInf (CStarSubmodule A E) fun _ ↦
      ⟨fun F hF _ hx ↦ mem_sInf.mp hx F hF,
        fun _ hG _ hx ↦ mem_sInf.mpr fun _ hF ↦ hG hF hx⟩ with
    top := ⊤
    le_top := fun _ _ _ ↦ trivial
    inf := (· ⊓ ·)
    le_inf := fun _ _ _ h₁₂ h₁₃ _ hx ↦ ⟨h₁₂ hx, h₁₃ hx⟩
    inf_le_left := fun _ _ _ ↦ And.left
    inf_le_right := fun _ _ _ ↦ And.right }

instance : Inhabited (CStarSubmodule A E) :=
  ⟨⊥⟩

@[simp]
theorem toSubmodule_iInf {ι : Sort*} (f : ι → CStarSubmodule A E) :
    (⨅ i, f i).toSubmodule = ⨅ i, (f i).toSubmodule := by
  simp only [iInf, toSubmodule_sInf, ← Set.range_comp, Function.comp_def]

@[simp]
theorem mem_iInf {ι : Sort*} {f : ι → CStarSubmodule A E} {x : E} :
    x ∈ ⨅ i, f i ↔ ∀ i, x ∈ f i := by
  simp [← mem_toSubmodule]

end Lattice

section LatticeBot

variable {A E : Type*} [AddCommGroup E] [Module ℂ E] [SMulZeroClass A E]

/-- When the coefficient action fixes `0`, `⊥` is the zero submodule `{0}`. -/
@[simp]
theorem toSubmodule_bot :
    (⊥ : CStarSubmodule A E).toSubmodule = ⊥ := by
  let zeroSub : CStarSubmodule A E :=
    { toSubmodule := ⊥
      smul_mem_coeff' := fun a _ hx ↦ by
        rw [Submodule.mem_carrier, SetLike.mem_coe, Submodule.mem_bot] at hx ⊢
        simp [hx] }
  exact le_antisymm (toSubmodule_le_toSubmodule.mpr (bot_le (a := zeroSub))) bot_le

@[simp]
theorem mem_bot {x : E} :
    x ∈ (⊥ : CStarSubmodule A E) ↔ x = 0 := by
  rw [← mem_toSubmodule, toSubmodule_bot, Submodule.mem_bot]

@[simp]
theorem coe_bot :
    ((⊥ : CStarSubmodule A E) : Set E) = {0} := by
  ext x
  exact mem_bot

theorem eq_bot_iff {F : CStarSubmodule A E} :
    F = ⊥ ↔ ∀ x ∈ F, x = 0 := by
  simp only [← toSubmodule_inj, toSubmodule_bot, Submodule.eq_bot_iff, mem_toSubmodule]

theorem disjoint_iff {F G : CStarSubmodule A E} :
    Disjoint F G ↔ Disjoint F.toSubmodule G.toSubmodule := by
  rw [disjoint_iff_inf_le, disjoint_iff_inf_le, ← toSubmodule_le_toSubmodule, toSubmodule_inf,
    toSubmodule_bot]

end LatticeBot

section LatticeSup

variable {A E : Type*} [AddCommGroup E] [Module ℂ E] [DistribSMul A E]

/-- When the coefficient action distributes over addition, the join `F ⊔ G` has underlying
subspace `F.toSubmodule ⊔ G.toSubmodule` (the algebraic sum `F + G`). -/
@[simp]
theorem toSubmodule_sup (F G : CStarSubmodule A E) :
    (F ⊔ G).toSubmodule = F.toSubmodule ⊔ G.toSubmodule := by
  let supSub : CStarSubmodule A E :=
    { toSubmodule := F.toSubmodule ⊔ G.toSubmodule
      smul_mem_coeff' := fun a _ hx ↦ by
        rw [Submodule.mem_carrier, SetLike.mem_coe, Submodule.mem_sup] at hx ⊢
        obtain ⟨u, hu, v, hv, rfl⟩ := hx
        exact ⟨a • u, F.smul_mem_coeff a hu, a • v, G.smul_mem_coeff a hv, (smul_add a u v).symm⟩ }
  have hF : F ≤ supSub := fun x hx ↦ Submodule.mem_sup_left hx
  have hG : G ≤ supSub := fun x hx ↦ Submodule.mem_sup_right hx
  exact le_antisymm (toSubmodule_le_toSubmodule.mpr (sup_le hF hG))
    (sup_le (toSubmodule_le_toSubmodule.mpr le_sup_left)
      (toSubmodule_le_toSubmodule.mpr le_sup_right))

theorem mem_sup {F G : CStarSubmodule A E} {z : E} :
    z ∈ F ⊔ G ↔ ∃ x ∈ F, ∃ y ∈ G, x + y = z := by
  simp only [← mem_toSubmodule, toSubmodule_sup, Submodule.mem_sup]

/-- When the coefficient action distributes over addition and commutes with complex scalar
multiplication, `sSup S` has underlying subspace `sSup (toSubmodule '' S)`. -/
@[simp]
theorem toSubmodule_sSup [SMulCommClass ℂ A E] (S : Set (CStarSubmodule A E)) :
    (sSup S).toSubmodule = sSup (toSubmodule '' S) := by
  let supSub : CStarSubmodule A E :=
    { toSubmodule := sSup (toSubmodule '' S)
      smul_mem_coeff' := fun a _ hx ↦ by
        rw [Submodule.mem_carrier, SetLike.mem_coe] at hx ⊢
        let _ : SMulCommClass A ℂ E := SMulCommClass.symm ℂ A E
        have hle : sSup (toSubmodule '' S) ≤
            (sSup (toSubmodule '' S)).comap (DistribSMul.toLinearMap ℂ E a) := by
          refine sSup_le ?_
          rintro _ ⟨F, hF, rfl⟩ y hy
          exact le_sSup (Set.mem_image_of_mem toSubmodule hF) (F.smul_mem_coeff a hy)
        exact hle hx }
  have hS : ∀ F ∈ S, F ≤ supSub := fun F hF ↦
    toSubmodule_le_toSubmodule.mp (le_sSup (Set.mem_image_of_mem toSubmodule hF))
  exact le_antisymm (toSubmodule_le_toSubmodule.mpr (sSup_le hS))
    (sSup_le <| by
      rintro _ ⟨F, hF, rfl⟩
      exact toSubmodule_le_toSubmodule.mpr (le_sSup hF))

@[simp]
theorem toSubmodule_iSup [SMulCommClass ℂ A E] {ι : Sort*} (f : ι → CStarSubmodule A E) :
    (⨆ i, f i).toSubmodule = ⨆ i, (f i).toSubmodule := by
  simp only [iSup, toSubmodule_sSup, ← Set.range_comp, Function.comp_def]

end LatticeSup

/-! ### Continuous subtype inclusions -/

section Normed

variable {A E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E]

/-- The subtype inclusion `F →ₗᵢ[ℂ] E` as a complex-linear isometry. -/
def subtypeₗᵢ (F : CStarSubmodule A E) : F →ₗᵢ[ℂ] E :=
  F.toSubmodule.subtypeₗᵢ

@[simp]
theorem subtypeₗᵢ_apply (F : CStarSubmodule A E) (x : F) : F.subtypeₗᵢ x = (x : E) :=
  (rfl)

@[simp]
theorem toLinearMap_subtypeₗᵢ (F : CStarSubmodule A E) : F.subtypeₗᵢ.toLinearMap = F.subtype :=
  (rfl)

theorem subtypeₗᵢ_smul_coeff (F : CStarSubmodule A E) (a : A) (x : F) :
    F.subtypeₗᵢ (a • x) = a • F.subtypeₗᵢ x :=
  (rfl)

/-- The subtype inclusion `F →L[ℂ] E` as a continuous complex-linear map. -/
def subtypeL (F : CStarSubmodule A E) : F →L[ℂ] E :=
  F.toSubmodule.subtypeL

@[simp]
theorem subtypeL_apply (F : CStarSubmodule A E) (x : F) : F.subtypeL x = (x : E) :=
  (rfl)

@[simp]
theorem toLinearMap_subtypeL (F : CStarSubmodule A E) : (F.subtypeL : F →ₗ[ℂ] E) = F.subtype :=
  (rfl)

@[simp]
theorem toContinuousLinearMap_subtypeₗᵢ (F : CStarSubmodule A E) :
    F.subtypeₗᵢ.toContinuousLinearMap = F.subtypeL :=
  (rfl)

@[simp]
theorem coe_subtypeL (F : CStarSubmodule A E) : (F.subtypeL : F → E) = F.subtype :=
  (rfl)

theorem subtypeL_injective (F : CStarSubmodule A E) : Function.Injective F.subtypeL :=
  Subtype.coe_injective

theorem range_subtypeL (F : CStarSubmodule A E) : F.subtypeL.range = F.toSubmodule :=
  F.toSubmodule.range_subtype

theorem subtypeL_smul_coeff (F : CStarSubmodule A E) (a : A) (x : F) :
    F.subtypeL (a • x) = a • F.subtypeL x :=
  (rfl)

end Normed

/-! ### Inherited Hilbert C⋆-module structure -/

section Inner

variable {A E : Type*} [AddCommGroup E] [Module ℂ E] [SMul A E] [Inner A E]

instance instInner (F : CStarSubmodule A E) : Inner A F where
  inner x y := inner A (x : E) (y : E)

@[simp]
theorem inner_coe (F : CStarSubmodule A E) (x y : F) :
    inner A x y = inner A (x : E) (y : E) :=
  (rfl)

theorem inner_subtype (F : CStarSubmodule A E) (x y : F) :
    inner A (F.subtype x) (F.subtype y) = inner A x y :=
  (rfl)

end Inner

section InnerNormed

variable {A E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [Inner A E]

theorem inner_subtypeₗᵢ (F : CStarSubmodule A E) (x y : F) :
    inner A (F.subtypeₗᵢ x) (F.subtypeₗᵢ y) = inner A x y :=
  (rfl)

theorem inner_subtypeL (F : CStarSubmodule A E) (x y : F) :
    inner A (F.subtypeL x) (F.subtypeL y) = inner A x y :=
  (rfl)

end InnerNormed

section CStarModule

variable {A E : Type*} [NonUnitalSemiring A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [SeminormedAddCommGroup E] [Module ℂ E] [SMul A E] [CStarModule A E]

/-- Every C⋆-submodule inherits the `CStarModule A` structure by restricting the ambient inner
product, norm, and coefficient action. -/
instance instCStarModule (F : CStarSubmodule A E) : CStarModule A F where
  inner_add_right := CStarModule.inner_add_right
  inner_self_nonneg := CStarModule.inner_self_nonneg
  inner_self {x} := by
    rw [inner_coe, CStarModule.inner_self, Subtype.ext_iff, ZeroMemClass.coe_zero]
  inner_op_smul_right := CStarModule.inner_op_smul_right
  inner_smul_right_complex := CStarModule.inner_smul_right_complex
  star_inner _ _ := CStarModule.star_inner _ _
  norm_eq_sqrt_norm_inner_self x := CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (x : E)

end CStarModule

section RightInner

variable {A E : Type*} [AddCommGroup E] [Module ℂ E] [SMul Aᵐᵒᵖ E] [Inner Aᵐᵒᵖ E]

theorem unop_inner_coe (F : CStarSubmodule Aᵐᵒᵖ E) (x y : F) :
    unop (inner Aᵐᵒᵖ x y) = unop (inner Aᵐᵒᵖ (x : E) (y : E)) :=
  (rfl)

end RightInner

/-! ### Topological closure -/

section TopologicalClosure

variable {A E : Type*} [AddCommGroup E] [Module ℂ E] [SMul A E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousConstSMul ℂ E] [ContinuousConstSMul A E]

/-- The topological closure of a C⋆-submodule is again a C⋆-submodule. -/
def topologicalClosure (F : CStarSubmodule A E) : CStarSubmodule A E where
  toSubmodule := F.toSubmodule.topologicalClosure
  smul_mem_coeff' a _ hx :=
    map_mem_closure (continuous_const_smul a) hx fun _ hy ↦ F.smul_mem_coeff a hy

@[simp]
theorem toSubmodule_topologicalClosure (F : CStarSubmodule A E) :
    F.topologicalClosure.toSubmodule = F.toSubmodule.topologicalClosure :=
  (rfl)

@[simp]
theorem coe_topologicalClosure (F : CStarSubmodule A E) :
    (F.topologicalClosure : Set E) = closure (F : Set E) :=
  (rfl)

theorem mem_topologicalClosure {F : CStarSubmodule A E} {x : E} :
    x ∈ F.topologicalClosure ↔ x ∈ closure (F : Set E) :=
  (Iff.rfl)

theorem isClosed_topologicalClosure (F : CStarSubmodule A E) :
    IsClosed (F.topologicalClosure : Set E) := by
  rw [coe_topologicalClosure]
  exact isClosed_closure

theorem le_topologicalClosure (F : CStarSubmodule A E) : F ≤ F.topologicalClosure := by
  intro x hx
  rw [mem_topologicalClosure]
  exact subset_closure hx

theorem topologicalClosure_minimal {F G : CStarSubmodule A E} (hFG : F ≤ G)
    (hG : IsClosed (G : Set E)) : F.topologicalClosure ≤ G := by
  intro x hx
  rw [mem_topologicalClosure] at hx
  exact closure_minimal hFG hG hx

theorem topologicalClosure_eq_self {F : CStarSubmodule A E} (hF : IsClosed (F : Set E)) :
    F.topologicalClosure = F :=
  le_antisymm (topologicalClosure_minimal le_rfl hF) (le_topologicalClosure F)

@[simp]
theorem topologicalClosure_eq_self_iff {F : CStarSubmodule A E} :
    F.topologicalClosure = F ↔ IsClosed (F : Set E) :=
  ⟨fun h ↦ h ▸ isClosed_topologicalClosure F, topologicalClosure_eq_self⟩

theorem topologicalClosure_mono {F G : CStarSubmodule A E} (h : F ≤ G) :
    F.topologicalClosure ≤ G.topologicalClosure :=
  topologicalClosure_minimal (h.trans (le_topologicalClosure G)) (isClosed_topologicalClosure G)

@[simp]
theorem topologicalClosure_idem (F : CStarSubmodule A E) :
    F.topologicalClosure.topologicalClosure = F.topologicalClosure :=
  topologicalClosure_eq_self (isClosed_topologicalClosure F)

end TopologicalClosure

/-! ### Kernels and ranges of coefficient-equivariant maps -/

section KerRange

variable {A E F : Type*} [AddCommGroup E] [Module ℂ E] [SMul A E]
  [AddCommGroup F] [Module ℂ F]

section Ker

variable [SMulZeroClass A F]

/-- The kernel of a complex-linear map commuting with the coefficient action, as a C⋆-submodule. -/
def ker (T : E →ₗ[ℂ] F) (hT : ∀ (a : A) (x : E), T (a • x) = a • T x) :
    CStarSubmodule A E where
  toSubmodule := LinearMap.ker T
  smul_mem_coeff' a x hx := by
    rw [Submodule.mem_carrier, SetLike.mem_coe, LinearMap.mem_ker] at hx ⊢
    rw [hT, hx, smul_zero]

@[simp]
theorem toSubmodule_ker (T : E →ₗ[ℂ] F) (hT : ∀ (a : A) (x : E), T (a • x) = a • T x) :
    (ker T hT).toSubmodule = LinearMap.ker T :=
  (rfl)

@[simp]
theorem mem_ker {T : E →ₗ[ℂ] F} {hT : ∀ (a : A) (x : E), T (a • x) = a • T x} {x : E} :
    x ∈ ker T hT ↔ T x = 0 :=
  (Iff.rfl)

end Ker

section Range

variable [SMul A F]

/-- The range of a complex-linear map commuting with the coefficient action, as a C⋆-submodule. -/
def range (T : E →ₗ[ℂ] F) (hT : ∀ (a : A) (x : E), T (a • x) = a • T x) :
    CStarSubmodule A F where
  toSubmodule := LinearMap.range T
  smul_mem_coeff' a _ hx := by
    obtain ⟨x, rfl⟩ := hx
    exact ⟨a • x, hT a x⟩

@[simp]
theorem toSubmodule_range (T : E →ₗ[ℂ] F) (hT : ∀ (a : A) (x : E), T (a • x) = a • T x) :
    (range T hT).toSubmodule = LinearMap.range T :=
  (rfl)

@[simp]
theorem mem_range {T : E →ₗ[ℂ] F} {hT : ∀ (a : A) (x : E), T (a • x) = a • T x} {y : F} :
    y ∈ range T hT ↔ ∃ x, T x = y :=
  (Iff.rfl)

end Range

end KerRange

/-! ### Closed right ideals as submodules of the right self-module -/

section RightIdeals

/-- Every C⋆-submodule of the right self-module `A` is closed under right multiplication in `A`. -/
theorem mul_mem_right {A : Type*} [NonUnitalRing A] [Module ℂ A]
    (I : CStarSubmodule Aᵐᵒᵖ A) {a : A} (ha : a ∈ I) (b : A) : a * b ∈ I :=
  I.op_smul_mem b ha

/-- View a complex-linear right ideal of `A` as a `CStarSubmodule Aᵐᵒᵖ A` of the right
self-module. -/
def ofRightIdeal {A : Type*} [NonUnitalRing A] [Module ℂ A] (I : Submodule ℂ A)
    (hmul : ∀ {a : A}, a ∈ I → ∀ b : A, a * b ∈ I) : CStarSubmodule Aᵐᵒᵖ A where
  toSubmodule := I
  smul_mem_coeff' b _ hx := hmul hx (unop b)

@[simp]
theorem mem_ofRightIdeal {A : Type*} [NonUnitalRing A] [Module ℂ A] (I : Submodule ℂ A)
    (hmul : ∀ {a : A}, a ∈ I → ∀ b : A, a * b ∈ I) {x : A} :
    x ∈ ofRightIdeal I hmul ↔ x ∈ I :=
  (Iff.rfl)

@[simp]
theorem toSubmodule_ofRightIdeal {A : Type*} [NonUnitalRing A] [Module ℂ A] (I : Submodule ℂ A)
    (hmul : ∀ {a : A}, a ∈ I → ∀ b : A, a * b ∈ I) :
    (ofRightIdeal I hmul).toSubmodule = I :=
  (rfl)

/-- Bundle a closed right ring ideal (an `AddSubgroup A` closed under right multiplication and
topologically closed) of a possibly nonunital C⋆-algebra `A` as a submodule of the right
self-module `CStarModule Aᵐᵒᵖ A`. -/
def ofClosedRightAddSubgroup {A : Type*} [NonUnitalCStarAlgebra A]
    (I : AddSubgroup A) (hI : IsClosed (I : Set A))
    (hmul : ∀ {a : A}, a ∈ I → ∀ b : A, a * b ∈ I) : CStarSubmodule Aᵐᵒᵖ A where
  carrier := I
  add_mem' := I.add_mem'
  zero_mem' := I.zero_mem'
  smul_mem' c _ hx := I.smul_mem_of_isClosed_right hI hmul c hx
  smul_mem_coeff' b _ hx := hmul hx (unop b)

@[simp]
theorem mem_ofClosedRightAddSubgroup {A : Type*} [NonUnitalCStarAlgebra A]
    (I : AddSubgroup A) (hI : IsClosed (I : Set A))
    (hmul : ∀ {a : A}, a ∈ I → ∀ b : A, a * b ∈ I) {x : A} :
    x ∈ ofClosedRightAddSubgroup I hI hmul ↔ x ∈ I :=
  (Iff.rfl)

theorem isClosed_ofClosedRightAddSubgroup {A : Type*} [NonUnitalCStarAlgebra A]
    (I : AddSubgroup A) (hI : IsClosed (I : Set A))
    (hmul : ∀ {a : A}, a ∈ I → ∀ b : A, a * b ∈ I) :
    IsClosed (ofClosedRightAddSubgroup I hI hmul : Set A) :=
  hI

/-- The right ideal `{x : A | p * x = x}` fixed by left multiplication by `p` (for a projection
`p`, this is `p A`), as a submodule of the right self-module `CStarModule Aᵐᵒᵖ A`. -/
def rightFixedSubmodule {A : Type*} [NonUnitalRing A] [Module ℂ A] [SMulCommClass ℂ A A]
    (p : A) : CStarSubmodule Aᵐᵒᵖ A :=
  ker (LinearMap.mulLeft ℂ p - LinearMap.id)
    (fun b x ↦ by
      simp [LinearMap.mulLeft_apply, smul_eq_mul_unop, mul_assoc, sub_mul])

@[simp]
theorem mem_rightFixedSubmodule {A : Type*} [NonUnitalRing A] [Module ℂ A] [SMulCommClass ℂ A A]
    {p x : A} : x ∈ rightFixedSubmodule p ↔ p * x = x := by
  refine (mem_ker (T := LinearMap.mulLeft ℂ p - LinearMap.id)).trans ?_
  rw [LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.id_apply, sub_eq_zero]

theorem isClosed_rightFixedSubmodule {A : Type*} [NonUnitalRing A] [Module ℂ A]
    [SMulCommClass ℂ A A] [TopologicalSpace A] [T2Space A] [SeparatelyContinuousMul A]
    (p : A) :
    IsClosed (rightFixedSubmodule p : Set A) := by
  have hset : (rightFixedSubmodule p : Set A) = {x : A | p * x = x} := by
    ext x
    exact mem_rightFixedSubmodule
  rw [hset]
  exact isClosed_eq (continuous_const_mul p) continuous_id

theorem mem_rightFixedSubmodule_iff_exists_mul {A : Type*} [NonUnitalRing A] [Module ℂ A]
    [SMulCommClass ℂ A A] {p x : A} (hp : IsIdempotentElem p) :
    x ∈ rightFixedSubmodule p ↔ ∃ a : A, p * a = x :=
  ⟨fun hx ↦ ⟨x, mem_rightFixedSubmodule.mp hx⟩,
    fun ⟨a, ha⟩ ↦ by rw [mem_rightFixedSubmodule, ← ha, ← mul_assoc, hp.eq]⟩

end RightIdeals

end CStarSubmodule

end TauCeti

namespace TwoSidedIdeal

/-- View a closed two-sided ideal of a (possibly nonunital) C⋆-algebra `A` as a submodule of the
right self-module `CStarModule Aᵐᵒᵖ A`. -/
def toCStarSubmodule {A : Type*} [NonUnitalCStarAlgebra A] (I : TwoSidedIdeal A)
    [IsClosed (I : Set A)] : TauCeti.CStarSubmodule Aᵐᵒᵖ A :=
  TauCeti.CStarSubmodule.ofRightIdeal I.toSubmodule fun hx b ↦ I.mul_mem_right _ b hx

@[simp]
theorem mem_toCStarSubmodule {A : Type*} [NonUnitalCStarAlgebra A] (I : TwoSidedIdeal A)
    [IsClosed (I : Set A)] {x : A} : x ∈ I.toCStarSubmodule ↔ x ∈ I :=
  (Iff.rfl)

@[simp]
theorem toSubmodule_toCStarSubmodule {A : Type*} [NonUnitalCStarAlgebra A] (I : TwoSidedIdeal A)
    [IsClosed (I : Set A)] : I.toCStarSubmodule.toSubmodule = I.toSubmodule :=
  (rfl)

theorem isClosed_toCStarSubmodule {A : Type*} [NonUnitalCStarAlgebra A] (I : TwoSidedIdeal A)
    [hI : IsClosed (I : Set A)] : IsClosed (I.toCStarSubmodule : Set A) :=
  hI

end TwoSidedIdeal

namespace Ideal

/-- View a right ideal `I : Ideal Aᵐᵒᵖ` of a unital complex algebra `A` as a `CStarSubmodule Aᵐᵒᵖ A`
of the right self-module `A`. -/
def toCStarSubmodule {A : Type*} [Ring A] [Algebra ℂ A] (I : Ideal Aᵐᵒᵖ) :
    TauCeti.CStarSubmodule Aᵐᵒᵖ A where
  carrier := {x : A | op x ∈ I}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, op_add] at hx hy ⊢
    exact I.add_mem hx hy
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, op_zero]
    exact I.zero_mem
  smul_mem' c x hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [Algebra.smul_def, Algebra.commutes, op_mul]
    exact I.mul_mem_left _ hx
  smul_mem_coeff' b x hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [smul_eq_mul_unop, op_mul, op_unop]
    exact I.mul_mem_left b hx

@[simp]
theorem mem_toCStarSubmodule {A : Type*} [Ring A] [Algebra ℂ A] (I : Ideal Aᵐᵒᵖ) {x : A} :
    x ∈ I.toCStarSubmodule ↔ op x ∈ I :=
  (Iff.rfl)

theorem isClosed_toCStarSubmodule {A : Type*} [Ring A] [Algebra ℂ A] [TopologicalSpace A]
    (I : Ideal Aᵐᵒᵖ) (hI : IsClosed (I : Set Aᵐᵒᵖ)) :
    IsClosed (I.toCStarSubmodule : Set A) :=
  hI.preimage continuous_op

end Ideal

namespace Submodule

/-- View an `A`-submodule of a complex vector space with a compatible unital `A`-module structure
(in particular, any `Submodule ℂ E`) as a `TauCeti.CStarSubmodule A E`. -/
def toCStarSubmodule {A E : Type*} [Semiring A] [AddCommGroup E] [Module ℂ E] [Module A E]
    [SMul ℂ A] [IsScalarTower ℂ A E] (K : Submodule A E) : TauCeti.CStarSubmodule A E where
  toSubmodule := K.restrictScalars ℂ
  smul_mem_coeff' a _ hx := K.smul_mem a hx

@[simp]
theorem mem_toCStarSubmodule {A E : Type*} [Semiring A] [AddCommGroup E] [Module ℂ E] [Module A E]
    [SMul ℂ A] [IsScalarTower ℂ A E] (K : Submodule A E) {x : E} :
    x ∈ K.toCStarSubmodule ↔ x ∈ K :=
  (Iff.rfl)

@[simp]
theorem toSubmodule_toCStarSubmodule {A E : Type*} [Semiring A] [AddCommGroup E] [Module ℂ E]
    [Module A E] [SMul ℂ A] [IsScalarTower ℂ A E] (K : Submodule A E) :
    K.toCStarSubmodule.toSubmodule = K.restrictScalars ℂ :=
  (rfl)

@[simp]
theorem coe_toCStarSubmodule {A E : Type*} [Semiring A] [AddCommGroup E] [Module ℂ E] [Module A E]
    [SMul ℂ A] [IsScalarTower ℂ A E] (K : Submodule A E) :
    (K.toCStarSubmodule : Set E) = K :=
  (rfl)

end Submodule
