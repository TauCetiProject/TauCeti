/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
public import TauCeti.Analysis.CStarAlgebra.Module.Submodule

import TauCeti.Analysis.CStarAlgebra.Module.Action

/-!
# Orthogonal complements in Hilbert C⋆-modules

Given a C⋆-submodule `F : TauCeti.CStarSubmodule A E` of a (pre-)Hilbert C⋆-module `E`, its
orthogonal complement `F.orthogonal` consists of all `y : E` satisfying `⟪x, y⟫_A = 0` for all
`x ∈ F`.

We establish the algebraic and metric properties of orthogonality and `F.orthogonal`:

* Orthogonal vectors satisfy the algebraic Pythagorean identity
  `⟪x + y, x + y⟫_A = ⟪x, x⟫_A + ⟪y, y⟫_A`, the summand bounds `‖x‖ ≤ ‖x + y‖` and `‖y‖ ≤ ‖x + y‖`,
  and the sub-Pythagorean bound `‖x + y‖ ^ 2 ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2`.
* `F.orthogonal` is always a norm-closed C⋆-submodule forming a self-adjoint Galois connection on
  `CStarSubmodule A E`, satisfying `F ⊓ F.orthogonal = ⊥`, `F ≤ F.orthogonal.orthogonal`, and
  `F.topologicalClosure.orthogonal = F.orthogonal`.
* The canonical addition map `F.addₗᵢ G hFG : C⋆ᵐᵒᵈ(A, F × G) →ₗᵢ[ℂ] E` for orthogonal
  submodules `G ≤ F.orthogonal` (and in particular `F.orthogonalAddₗᵢ`) preserves the `A`-valued
  inner product, the `A`-action, and the module norm; hence `F ⊔ G` is norm-closed whenever `F`
  and `G` are complete (in particular, `F ⊔ F.orthogonal` is closed when `E` is complete and `F`
  is closed).

For orthogonal complementability (`F ⊔ F.orthogonal = ⊤`), canonical projections, characterizations
via adjoints and self-adjoint idempotents, and concrete examples/counterexamples, see
`TauCeti.Analysis.CStarAlgebra.Module.Complemented`.

## Main declarations

* `CStarModule.inner_add_self_of_inner_eq_zero`,
  `CStarModule.norm_le_norm_add_left_of_inner_eq_zero`,
  `CStarModule.norm_le_norm_add_right_of_inner_eq_zero`,
  `CStarModule.norm_add_sq_le_of_inner_eq_zero`: Pythagorean identities and norm bounds for
  orthogonal vectors.
* `TauCeti.CStarSubmodule.orthogonal`: the orthogonal complement of a C⋆-submodule, with its
  Galois connection (`orthogonal_gc`), closedness (`isClosed_orthogonal`), and invariance under
  closure (`orthogonal_topologicalClosure`).
* `TauCeti.CStarSubmodule.addₗᵢ`, `TauCeti.CStarSubmodule.isClosed_sup_of_le_orthogonal`,
  `TauCeti.CStarSubmodule.orthogonalAddₗᵢ`, `TauCeti.CStarSubmodule.isClosed_sup_orthogonal`,
  `TauCeti.CStarSubmodule.isClosed_sup_orthogonal_of_isClosed`: orthogonal direct-sum isometries and
  closedness of `F ⊔ G` and `F ⊔ F.orthogonal`.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1 and
  Chapter 3.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Chapter 2.
-/

public section

open MulOpposite
open scoped WithCStarModule

namespace CStarModule

section Semiring

variable {A E : Type*} [NonUnitalSemiring A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm A]
  [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]

/-- Orthogonal vectors satisfy the algebraic Pythagorean identity
`⟪x + y, x + y⟫_A = ⟪x, x⟫_A + ⟪y, y⟫_A`. -/
theorem inner_add_self_of_inner_eq_zero {x y : E} (h : inner A x y = 0) :
    inner A (x + y) (x + y) = inner A x x + inner A y y := by
  have hleft (u v w : E) : inner A (u + v) w = inner A u w + inner A v w := by
    rw [← star_star (r := inner A (u + v) w), star_inner, inner_add_right, star_add, star_inner,
      star_inner]
  have hyx : inner A y x = 0 := by rw [← star_inner, h, star_zero]
  simp [hleft, inner_add_right, h, hyx]

end Semiring

section Algebraic

variable {A E : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A] [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]

/-- Orthogonality for the C⋆-module inner product is symmetric: `⟪x, y⟫_A = 0 → ⟪y, x⟫_A = 0`. -/
theorem isRefl_innerₛₗ : (CStarModule.innerₛₗ (A := A) (E := E)).IsRefl := fun x y h ↦ by
  rw [innerₛₗ_apply] at h ⊢
  rw [← star_inner, h, star_zero]

end Algebraic

section Norm

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
  [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]

/-- Sub-Pythagorean norm inequality for orthogonal vectors: if `⟪x, y⟫_A = 0`, then
`‖x + y‖ ^ 2 ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2`. -/
theorem norm_add_sq_le_of_inner_eq_zero {x y : E} (h : inner A x y = 0) :
    ‖x + y‖ ^ 2 ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [norm_sq_eq A, norm_sq_eq A, norm_sq_eq A, inner_add_self_of_inner_eq_zero h]
  exact norm_add_le _ _

/-- Orthogonal summands are bounded in norm by their sum: if `⟪x, y⟫_A = 0`, then
`‖x‖ ≤ ‖x + y‖`. -/
theorem norm_le_norm_add_left_of_inner_eq_zero [StarOrderedRing A] {x y : E}
    (h : inner A x y = 0) : ‖x‖ ≤ ‖x + y‖ := by
  rw [← sq_le_sq₀ (CStarModule.norm_nonneg A) (CStarModule.norm_nonneg A), norm_sq_eq A,
    norm_sq_eq A, inner_add_self_of_inner_eq_zero h]
  exact CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (le_add_of_nonneg_right inner_self_nonneg) inner_self_nonneg

/-- Orthogonal summands are bounded in norm by their sum: if `⟪x, y⟫_A = 0`, then
`‖y‖ ≤ ‖x + y‖`. -/
theorem norm_le_norm_add_right_of_inner_eq_zero [StarOrderedRing A] {x y : E}
    (h : inner A x y = 0) : ‖y‖ ≤ ‖x + y‖ := by
  rw [add_comm]
  exact norm_le_norm_add_left_of_inner_eq_zero (A := A) (by rw [← star_inner, h, star_zero])

end Norm

end CStarModule

namespace Submodule

section Algebraic

variable {A E : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A] [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]

/-- The orthogonal complement of any complex submodule with respect to `CStarModule.innerₛₗ` is
stable under the coefficient action `SMul A E`. -/
theorem smul_mem_orthogonalBilin (S : Submodule ℂ E) (a : A) {y : E}
    (hy : y ∈ S.orthogonalBilin (CStarModule.innerₛₗ (A := A))) :
    a • y ∈ S.orthogonalBilin (CStarModule.innerₛₗ (A := A)) := by
  rw [Submodule.mem_orthogonalBilin] at hy ⊢
  intro x hx
  rw [CStarModule.innerₛₗ_apply, CStarModule.inner_op_smul_right,
    ← CStarModule.innerₛₗ_apply, hy x hx, mul_zero]

end Algebraic

section Analytic

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]

/-- The orthogonal complement of any complex submodule with respect to `CStarModule.innerₛₗ` is
closed in the module norm. -/
theorem isClosed_orthogonalBilin (S : Submodule ℂ E) :
    IsClosed (S.orthogonalBilin (CStarModule.innerₛₗ (A := A)) : Set E) := by
  have heq : (S.orthogonalBilin (CStarModule.innerₛₗ (A := A)) : Set E) =
      ⋂ x ∈ S, {y : E | inner A x y = 0} := by
    ext y
    simp only [SetLike.mem_coe, Submodule.mem_orthogonalBilin, CStarModule.innerₛₗ_apply,
      Set.mem_iInter, Set.mem_ofPred_eq]
  rw [heq]
  exact isClosed_biInter fun x _ ↦
    isClosed_eq (CStarModule.continuous_inner.comp (continuous_const.prodMk continuous_id))
      continuous_const

end Analytic

end Submodule

namespace TauCeti.CStarSubmodule

/-! ### Orthogonal complements -/

section OrthogonalAlgebraic

variable {A E : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [Norm A] [AddCommGroup E] [Module ℂ E] [SMul A E] [Norm E] [CStarModule A E]

/-- The orthogonal complement of a C⋆-submodule `F`, consisting of all `y : E` such that
`⟪x, y⟫_A = 0` for all `x ∈ F`. -/
def orthogonal (F : CStarSubmodule A E) : CStarSubmodule A E where
  toSubmodule := F.toSubmodule.orthogonalBilin (CStarModule.innerₛₗ (A := A))
  smul_mem_coeff' a _ hy := F.toSubmodule.smul_mem_orthogonalBilin a hy

theorem toSubmodule_orthogonal (F : CStarSubmodule A E) :
    F.orthogonal.toSubmodule = F.toSubmodule.orthogonalBilin (CStarModule.innerₛₗ (A := A)) :=
  (rfl)

@[simp]
theorem mem_orthogonal {F : CStarSubmodule A E} {y : E} :
    y ∈ F.orthogonal ↔ ∀ x ∈ F, inner A x y = 0 :=
  (Iff.rfl)

theorem mem_orthogonal' {F : CStarSubmodule A E} {y : E} :
    y ∈ F.orthogonal ↔ ∀ x ∈ F, inner A y x = 0 := by
  rw [mem_orthogonal]
  refine forall₂_congr fun x _ ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← CStarModule.star_inner, h, star_zero]
  · rw [← CStarModule.star_inner, h, star_zero]

theorem inner_right_of_mem_orthogonal {F : CStarSubmodule A E} {x y : E} (hx : x ∈ F)
    (hy : y ∈ F.orthogonal) : inner A x y = 0 :=
  mem_orthogonal.mp hy x hx

theorem inner_left_of_mem_orthogonal {F : CStarSubmodule A E} {x y : E} (hx : x ∈ F)
    (hy : y ∈ F.orthogonal) : inner A y x = 0 :=
  mem_orthogonal'.mp hy x hx

theorem sub_mem_orthogonal_of_inner_right {F : CStarSubmodule A E} {x y : E}
    (h : ∀ u ∈ F, inner A u x = inner A u y) : x - y ∈ F.orthogonal := by
  rw [mem_orthogonal]
  intro u hu
  rw [CStarModule.inner_sub_right, h u hu, sub_self]

theorem sub_mem_orthogonal_of_inner_left {F : CStarSubmodule A E} {x y : E}
    (h : ∀ u ∈ F, inner A x u = inner A y u) : x - y ∈ F.orthogonal := by
  rw [mem_orthogonal']
  intro u hu
  rw [CStarModule.inner_sub_left, h u hu, sub_self]

theorem le_orthogonal_iff {F G : CStarSubmodule A E} :
    F ≤ G.orthogonal ↔ G ≤ F.orthogonal :=
  ⟨fun h _ hy _ hx ↦ inner_left_of_mem_orthogonal hy (h hx),
    fun h _ hx _ hy ↦ inner_left_of_mem_orthogonal hx (h hy)⟩

/-- `orthogonal` forms a self-adjoint Galois connection on `CStarSubmodule A E`. -/
theorem orthogonal_gc :
    @GaloisConnection (CStarSubmodule A E) (CStarSubmodule A E)ᵒᵈ _ _
      orthogonal (fun F ↦ (OrderDual.ofDual F).orthogonal) :=
  fun _ _ ↦ le_orthogonal_iff

theorem orthogonal_antitone : Antitone (orthogonal : CStarSubmodule A E → CStarSubmodule A E) :=
  orthogonal_gc.monotone_l

@[gcongr]
theorem orthogonal_le {F G : CStarSubmodule A E} (h : F ≤ G) : G.orthogonal ≤ F.orthogonal :=
  orthogonal_antitone h

theorem le_orthogonal_orthogonal (F : CStarSubmodule A E) : F ≤ F.orthogonal.orthogonal :=
  orthogonal_gc.le_u_l F

theorem orthogonal_orthogonal_monotone {F G : CStarSubmodule A E} (h : F ≤ G) :
    F.orthogonal.orthogonal ≤ G.orthogonal.orthogonal :=
  orthogonal_le (orthogonal_le h)

@[simp]
theorem orthogonal_orthogonal_orthogonal (F : CStarSubmodule A E) :
    F.orthogonal.orthogonal.orthogonal = F.orthogonal :=
  orthogonal_gc.l_u_l_eq_l F

@[simp]
theorem orthogonal_bot : (⊥ : CStarSubmodule A E).orthogonal = ⊤ :=
  orthogonal_gc.l_bot

@[simp]
theorem orthogonal_top : (⊤ : CStarSubmodule A E).orthogonal = ⊥ := by
  let _ := CStarModule.distribSMul A E
  rw [eq_bot_iff]
  intro x hx
  exact (CStarModule.inner_self (A := A)).mp (mem_orthogonal.mp hx x (mem_top x))

@[simp]
theorem orthogonal_eq_top_iff {F : CStarSubmodule A E} : F.orthogonal = ⊤ ↔ F = ⊥ := by
  let _ := CStarModule.distribSMul A E
  refine ⟨fun h ↦ eq_bot_iff.mpr fun x hx ↦ ?_, fun h ↦ by rw [h, orthogonal_bot]⟩
  exact (CStarModule.inner_self (A := A)).mp (mem_orthogonal.mp (h ▸ mem_top x) x hx)

@[simp]
theorem inf_orthogonal_eq_bot (F : CStarSubmodule A E) : F ⊓ F.orthogonal = ⊥ := by
  let _ := CStarModule.distribSMul A E
  rw [eq_bot_iff]
  intro x hx
  exact (CStarModule.inner_self (A := A)).mp (inner_right_of_mem_orthogonal hx.1 hx.2)

theorem orthogonal_disjoint (F : CStarSubmodule A E) : Disjoint F F.orthogonal := by
  rw [disjoint_iff_inf_le, inf_orthogonal_eq_bot]

theorem orthogonal_sup (F G : CStarSubmodule A E) :
    (F ⊔ G).orthogonal = F.orthogonal ⊓ G.orthogonal :=
  orthogonal_gc.l_sup

theorem orthogonal_sSup (S : Set (CStarSubmodule A E)) :
    (sSup S).orthogonal = ⨅ F ∈ S, F.orthogonal :=
  orthogonal_gc.l_sSup

theorem orthogonal_iSup {ι : Sort*} (f : ι → CStarSubmodule A E) :
    (⨆ i, f i).orthogonal = ⨅ i, (f i).orthogonal :=
  orthogonal_gc.l_iSup

end OrthogonalAlgebraic

section OrthogonalRight

variable {A E : Type*} [NonUnitalSeminormedRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A]
  [PartialOrder A] [AddCommGroup E] [Module ℂ E] [SMul Aᵐᵒᵖ E] [Norm E] [CStarModule Aᵐᵒᵖ E]

/-- In a right C⋆-module (`CStarModule Aᵐᵒᵖ E`), `y ∈ F.orthogonal` means `⟨x, y⟩_A = 0` for all
`x ∈ F`. -/
theorem mem_orthogonal_unop_iff {F : CStarSubmodule Aᵐᵒᵖ E} {y : E} :
    y ∈ F.orthogonal ↔ ∀ x ∈ F, unop (inner Aᵐᵒᵖ x y) = 0 := by
  rw [mem_orthogonal]
  refine forall₂_congr fun x _ ↦ ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
  exact unop_injective (by simpa using h)

end OrthogonalRight

section OrthogonalAnalytic

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]

/-- The orthogonal complement of any C⋆-submodule is norm-closed. -/
theorem isClosed_orthogonal (F : CStarSubmodule A E) : IsClosed (F.orthogonal : Set E) :=
  F.toSubmodule.isClosed_orthogonalBilin

instance instOrthogonalCompleteSpace [CompleteSpace E] (F : CStarSubmodule A E) :
    CompleteSpace F.orthogonal :=
  (isClosed_orthogonal F).completeSpace_coe

section

local instance : ContinuousConstSMul A E := ⟨CStarModule.continuous_const_smul⟩

/-- Taking the topological closure does not change the orthogonal complement. -/
@[simp]
theorem orthogonal_topologicalClosure (F : CStarSubmodule A E) :
    F.topologicalClosure.orthogonal = F.orthogonal := by
  refine le_antisymm (orthogonal_le (le_topologicalClosure F)) fun y hy ↦ ?_
  rw [mem_orthogonal] at hy ⊢
  intro x hx
  rw [mem_topologicalClosure] at hx
  have hclosed : IsClosed {z : E | inner A z y = 0} :=
    isClosed_eq (CStarModule.continuous_inner.comp (continuous_id.prodMk continuous_const))
      continuous_const
  exact closure_minimal (fun z hz ↦ hy z hz) hclosed hx

/-- The norm closure of `F` is always contained in its double orthogonal complement `F⊥⊥`. -/
theorem topologicalClosure_le_orthogonal_orthogonal (F : CStarSubmodule A E) :
    F.topologicalClosure ≤ F.orthogonal.orthogonal :=
  topologicalClosure_minimal (le_orthogonal_orthogonal F) (isClosed_orthogonal F.orthogonal)

end

/-! ### Orthogonal direct-sum isometry and closedness of `F ⊔ G` -/

/-- The canonical addition map `C⋆ᵐᵒᵈ(A, F × G) →ₗᵢ[ℂ] E` sending `(x, y)` to `x + y` for
orthogonal C⋆-submodules `G ≤ F.orthogonal`. It preserves both the `A`-valued inner product and
the `A`-action. -/
noncomputable def addₗᵢ (F G : CStarSubmodule A E) (hFG : G ≤ F.orthogonal) :
    C⋆ᵐᵒᵈ(A, F × G) →ₗᵢ[ℂ] E where
  toFun p := (p.1 : E) + (p.2 : E)
  map_add' p q := by
    rw [WithCStarModule.add_fst, WithCStarModule.add_snd]
    exact add_add_add_comm (p.1 : E) (q.1 : E) (p.2 : E) (q.2 : E)
  map_smul' c p := by
    simp only [WithCStarModule.smul_fst, WithCStarModule.smul_snd, SetLike.val_smul,
      RingHom.id_apply, smul_add]
  norm_map' p := by
    have horth : inner A (p.1 : E) (p.2 : E) = 0 :=
      inner_right_of_mem_orthogonal p.1.property (hFG p.2.property)
    have hnorm : ‖(p.1 : E) + (p.2 : E)‖ = ‖p‖ := by
      rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A),
        CStarModule.inner_add_self_of_inner_eq_zero horth, WithCStarModule.prod_norm]
      rfl
    exact hnorm

@[simp]
theorem addₗᵢ_apply (F G : CStarSubmodule A E) (hFG : G ≤ F.orthogonal) (p : C⋆ᵐᵒᵈ(A, F × G)) :
    F.addₗᵢ G hFG p = (p.1 : E) + (p.2 : E) :=
  (rfl)

theorem inner_addₗᵢ (F G : CStarSubmodule A E) (hFG : G ≤ F.orthogonal)
    (p q : C⋆ᵐᵒᵈ(A, F × G)) :
    inner A (F.addₗᵢ G hFG p) (F.addₗᵢ G hFG q) = inner A p q := by
  have h12 : inner A (p.1 : E) (q.2 : E) = 0 :=
    inner_right_of_mem_orthogonal p.1.property (hFG q.2.property)
  have h21 : inner A (p.2 : E) (q.1 : E) = 0 :=
    inner_left_of_mem_orthogonal q.1.property (hFG p.2.property)
  simp [addₗᵢ_apply, CStarModule.inner_add_left, CStarModule.inner_add_right, h12, h21,
    WithCStarModule.prod_inner]

theorem addₗᵢ_smul_coeff (F G : CStarSubmodule A E) (hFG : G ≤ F.orthogonal) (a : A)
    (p : C⋆ᵐᵒᵈ(A, F × G)) :
    F.addₗᵢ G hFG (a • p) = a • F.addₗᵢ G hFG p := by
  let _ := CStarModule.distribSMul A E
  simp [addₗᵢ_apply, smul_add]

@[simp]
theorem range_addₗᵢ (F G : CStarSubmodule A E) (hFG : G ≤ F.orthogonal) :
    LinearMap.range (F.addₗᵢ G hFG).toLinearMap = (F ⊔ G).toSubmodule := by
  let _ := CStarModule.distribSMul A E
  ext z
  simp only [LinearMap.mem_range, LinearIsometry.coe_toLinearMap, addₗᵢ_apply,
    mem_toSubmodule, mem_sup]
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1, p.1.property, p.2, p.2.property, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨(WithCStarModule.equiv A (F × G)).symm (⟨x, hx⟩, ⟨y, hy⟩), rfl⟩

/-- If `F` and `G` are complete orthogonal C⋆-submodules (`G ≤ F.orthogonal`), then their
algebraic sum `F ⊔ G` is norm-closed in `E`. -/
theorem isClosed_sup_of_le_orthogonal {F G : CStarSubmodule A E} (hFG : G ≤ F.orthogonal)
    [CompleteSpace F] [CompleteSpace G] :
    IsClosed ((F ⊔ G : CStarSubmodule A E) : Set E) := by
  have hrange : ((F ⊔ G : CStarSubmodule A E) : Set E) = Set.range (F.addₗᵢ G hFG) := by
    rw [← coe_toSubmodule, ← range_addₗᵢ F G hFG]
    rfl
  rw [hrange]
  exact (F.addₗᵢ G hFG).isometry.isUniformInducing.isComplete_range.isClosed

/-- If `E` is complete and `F`, `G` are closed orthogonal C⋆-submodules (`G ≤ F.orthogonal`), then
their algebraic sum `F ⊔ G` is norm-closed in `E`. -/
theorem isClosed_sup_of_isClosed [CompleteSpace E] {F G : CStarSubmodule A E}
    (hFG : G ≤ F.orthogonal) (hF : IsClosed (F : Set E)) (hG : IsClosed (G : Set E)) :
    IsClosed ((F ⊔ G : CStarSubmodule A E) : Set E) := by
  have _ : CompleteSpace F := hF.completeSpace_coe
  have _ : CompleteSpace G := hG.completeSpace_coe
  exact isClosed_sup_of_le_orthogonal hFG

/-- The canonical addition map `C⋆ᵐᵒᵈ(A, F × F.orthogonal) →ₗᵢ[ℂ] E` sending `(x, y)` to `x + y`.
It preserves both the `A`-valued inner product and the `A`-action. -/
noncomputable def orthogonalAddₗᵢ (F : CStarSubmodule A E) :
    C⋆ᵐᵒᵈ(A, F × F.orthogonal) →ₗᵢ[ℂ] E :=
  F.addₗᵢ F.orthogonal le_rfl

@[simp]
theorem orthogonalAddₗᵢ_apply (F : CStarSubmodule A E) (p : C⋆ᵐᵒᵈ(A, F × F.orthogonal)) :
    F.orthogonalAddₗᵢ p = (p.1 : E) + (p.2 : E) :=
  F.addₗᵢ_apply F.orthogonal le_rfl p

theorem inner_orthogonalAddₗᵢ (F : CStarSubmodule A E) (p q : C⋆ᵐᵒᵈ(A, F × F.orthogonal)) :
    inner A (F.orthogonalAddₗᵢ p) (F.orthogonalAddₗᵢ q) = inner A p q :=
  F.inner_addₗᵢ F.orthogonal le_rfl p q

theorem orthogonalAddₗᵢ_smul_coeff (F : CStarSubmodule A E) (a : A)
    (p : C⋆ᵐᵒᵈ(A, F × F.orthogonal)) :
    F.orthogonalAddₗᵢ (a • p) = a • F.orthogonalAddₗᵢ p :=
  F.addₗᵢ_smul_coeff F.orthogonal le_rfl a p

@[simp]
theorem range_orthogonalAddₗᵢ (F : CStarSubmodule A E) :
    LinearMap.range F.orthogonalAddₗᵢ.toLinearMap = (F ⊔ F.orthogonal).toSubmodule :=
  F.range_addₗᵢ F.orthogonal le_rfl

/-- If `F` and `F.orthogonal` are complete (in particular, if `E` is complete and `F` is closed),
then the algebraic orthogonal sum `F ⊔ F.orthogonal` is norm-closed in `E`. -/
theorem isClosed_sup_orthogonal (F : CStarSubmodule A E) [CompleteSpace F]
    [CompleteSpace F.orthogonal] :
    IsClosed ((F ⊔ F.orthogonal : CStarSubmodule A E) : Set E) :=
  isClosed_sup_of_le_orthogonal (F := F) (G := F.orthogonal) le_rfl

/-- If `E` is complete and `F` is closed, then the algebraic orthogonal sum `F ⊔ F.orthogonal` is
norm-closed in `E`. -/
theorem isClosed_sup_orthogonal_of_isClosed [CompleteSpace E] {F : CStarSubmodule A E}
    (hF : IsClosed (F : Set E)) :
    IsClosed ((F ⊔ F.orthogonal : CStarSubmodule A E) : Set E) :=
  isClosed_sup_of_isClosed le_rfl hF (isClosed_orthogonal F)

end OrthogonalAnalytic

end TauCeti.CStarSubmodule
