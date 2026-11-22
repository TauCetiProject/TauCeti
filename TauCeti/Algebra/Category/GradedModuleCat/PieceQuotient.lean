/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Basic
public import TauCeti.Algebra.Module.GradedModule.Nakayama
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Degreewise quotients of graded modules by the positive-degree action

For a graded `𝒜`-module `M` over a `ℤ`-graded `k`-algebra `A`, the degree-`p` piece `Mₚ` and the
positive-degree action `A₊ M` are submodules over the degree-zero subalgebra
`SetLike.GradeZero.subalgebra 𝒜`. Their quotient `PieceQuotient M p := (M / A₊ M)ₚ` is functorial
with respect to morphisms in `GradedModuleCat 𝒜` via `Submodule.mapQ`.

## Main definitions

* `TauCeti.GradedModuleCat.pieceSubmodule`: the homogeneous piece `Mₚ` as an `A₀`-submodule of `M`.
* `TauCeti.GradedModuleCat.positiveSubmodule`: the positive-degree action `A₊ M` as an
  `A₀`-submodule of `M`.
* `TauCeti.GradedModuleCat.PieceQuotient`: the degree-`p` quotient `(M / A₊ M)ₚ` as an
  `A₀`-module.
* `TauCeti.GradedModuleCat.pieceQuotientMap`: the `A₀`-linear projection
  `M →ₗ[A₀] PieceQuotient M p`.
* `TauCeti.GradedModuleCat.pieceQuotientHom`: the `A₀`-linear map on `PieceQuotient` induced by a
  morphism in `GradedModuleCat 𝒜`.
-/

public section

noncomputable section

namespace TauCeti.GradedModuleCat

open CategoryTheory _root_.DirectSum

universe uk uA v

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- The homogeneous piece `Mₚ`, as a module over the degree-zero subalgebra. -/
@[expose]
def pieceSubmodule (M : GradedModuleCat.{v} 𝒜) (p : ℤ) :
    Submodule (SetLike.GradeZero.subalgebra 𝒜) M where
  __ := M.grading.piece p
  smul_mem' c x hx := by
    have hx : x ∈ M.grading.piece p := hx
    rw [Subalgebra.smul_def]
    simpa using SetLike.GradedSMul.smul_mem (A := 𝒜) c.property hx

/-- Membership in `pieceSubmodule M p` is membership in `M.grading.piece p`. -/
theorem mem_pieceSubmodule {M : GradedModuleCat.{v} 𝒜} {p : ℤ} {x : M} :
    x ∈ pieceSubmodule M p ↔ x ∈ M.grading.piece p :=
  Iff.rfl

/-- The positive-degree action `A₊ M`, as a module over the degree-zero subalgebra. -/
@[expose]
def positiveSubmodule (M : GradedModuleCat.{v} 𝒜) :
    Submodule (SetLike.GradeZero.subalgebra 𝒜) M where
  __ := (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)
  smul_mem' c x hx := by
    rw [Subalgebra.smul_def]
    exact InternalGrading.smul_mem_positive_smul_top c.property hx

/-- Membership in `positiveSubmodule M` is membership in `A₊ M`. -/
theorem mem_positiveSubmodule {M : GradedModuleCat.{v} 𝒜} {x : M} :
    x ∈ positiveSubmodule M ↔ x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) :=
  Iff.rfl

/-- The homogeneous piece `(M / A₊ M)ₚ`, as a module over the degree-zero subalgebra. -/
abbrev PieceQuotient (M : GradedModuleCat.{v} 𝒜) (p : ℤ) :=
  pieceSubmodule M p ⧸ (positiveSubmodule M).comap (pieceSubmodule M p).subtype

/-- Projection to the degree-`p` piece of `M / A₊ M`. -/
def pieceQuotientMap (M : GradedModuleCat.{v} 𝒜) (p : ℤ) :
    M →ₗ[SetLike.GradeZero.subalgebra 𝒜] PieceQuotient M p :=
  Submodule.mkQ _ ∘ₗ
    { toFun x := ⟨decompose M.grading.piece x p, (decompose M.grading.piece x p).property⟩
      map_add' x y := by ext; simp
      map_smul' c x := by
        ext
        -- Multiplication by a degree-zero scalar is homogeneous of degree zero.
        have hf : LinearMap.IsHomogeneous (Algebra.lsmul k k M (c : A))
            M.grading.piece M.grading.piece 0 :=
          LinearMap.isHomogeneous_def.mpr fun q z hz => by
            simpa [add_comm] using SetLike.GradedSMul.smul_mem (A := 𝒜) c.property hz
        have h := hf.map_decompose p x
        rw [add_zero] at h
        simpa [Subalgebra.smul_def] using h.symm }

/-- On a degree-`p` element, `pieceQuotientMap M p` is the quotient class in `PieceQuotient M p`. -/
theorem pieceQuotientMap_of_mem {M : GradedModuleCat.{v} 𝒜} {p : ℤ} {x : M}
    (hx : x ∈ M.grading.piece p) :
    pieceQuotientMap M p x = Submodule.Quotient.mk ⟨x, mem_pieceSubmodule.mpr hx⟩ := by
  simp [pieceQuotientMap, decompose_of_mem_same _ hx]

/-- On an element homogeneous of degree `q ≠ p`, `pieceQuotientMap M p` vanishes. -/
theorem pieceQuotientMap_of_mem_ne {M : GradedModuleCat.{v} 𝒜} {p q : ℤ} {x : M}
    (hx : x ∈ M.grading.piece q) (hqp : q ≠ p) : pieceQuotientMap M p x = 0 := by
  simp [pieceQuotientMap, decompose_of_mem_ne _ hx hqp]

/-- Elements of `A₊ M` map to zero under `pieceQuotientMap M p`. -/
theorem pieceQuotientMap_eq_zero {M : GradedModuleCat.{v} 𝒜} {p : ℤ} {x : M}
    (hx : x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) :
    pieceQuotientMap M p x = 0 := by
  simp only [pieceQuotientMap, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  exact InternalGrading.isHomogeneous_positive_smul_top 𝒜 p hx

private def pieceMap {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) (p : ℤ) :
    pieceSubmodule M p →ₗ[SetLike.GradeZero.subalgebra 𝒜] pieceSubmodule N p :=
  (f.hom.restrictScalars (SetLike.GradeZero.subalgebra 𝒜)).restrict fun _ hx ↦ map_mem f hx

/-- The `A₀`-linear map `PieceQuotient M p →ₗ[A₀] PieceQuotient N p` induced by a graded
morphism `f : M ⟶ N`. -/
def pieceQuotientHom {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) (p : ℤ) :
    PieceQuotient M p →ₗ[SetLike.GradeZero.subalgebra 𝒜] PieceQuotient N p :=
  Submodule.mapQ _ _ (pieceMap f p) (fun _ hx ↦ map_mem_positive_smul_top f hx)

/-- `pieceQuotientHom f p` acts on quotient classes by applying `f.hom`. -/
@[simp]
theorem pieceQuotientHom_apply {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) (p : ℤ)
    (x : pieceSubmodule M p) :
    pieceQuotientHom f p (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨f.hom x.val, map_mem f x.property⟩ :=
  Submodule.mapQ_apply _ _ _ _

/-- `pieceQuotientHom` sends the identity morphism to the identity linear map. -/
@[simp]
theorem pieceQuotientHom_id (M : GradedModuleCat.{v} 𝒜) (p : ℤ) :
    pieceQuotientHom (𝟙 M) p = LinearMap.id :=
  Submodule.mapQ_id _

/-- `pieceQuotientHom` respects composition of graded morphisms. -/
@[simp]
theorem pieceQuotientHom_comp {M N P : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) (g : N ⟶ P) (p : ℤ) :
    pieceQuotientHom (f ≫ g) p = (pieceQuotientHom g p).comp (pieceQuotientHom f p) := by
  have hcomp : pieceMap (f ≫ g) p = (pieceMap g p).comp (pieceMap f p) := by ext x; rfl
  refine Eq.trans ?_ (Submodule.mapQ_comp _ _ _ (pieceMap f p) (pieceMap g p)
    (fun _ hx ↦ map_mem_positive_smul_top f hx)
    (fun _ hx ↦ map_mem_positive_smul_top g hx))
  dsimp only [pieceQuotientHom]
  congr 1

end TauCeti.GradedModuleCat
