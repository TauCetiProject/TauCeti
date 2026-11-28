/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.Algebra.Module.GradedModule.PositiveAction
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Degreewise quotients of internally graded modules by the positive-degree action

For an internally `ℤ`-graded module `G : InternalGrading k M ℤ` over a `ℤ`-graded `k`-algebra
`𝒜 : ℤ → Submodule k A`, the degree-`p` piece `Mₚ` and the positive-degree action `A₊ M` are
submodules over the degree-zero subalgebra `SetLike.GradeZero.subalgebra 𝒜`. Their quotient
`PieceQuotient G 𝒜 p := (M / A₊ M)ₚ` inherits an `A₀`-module structure together with a surjective
`A₀`-linear projection `pieceQuotientMap G 𝒜 p : M →ₗ[A₀] PieceQuotient G 𝒜 p`.

## Main definitions

* `TauCeti.InternalGrading.pieceSubmodule`: the homogeneous piece `G.piece p` as an
  `A₀`-submodule of `M`.
* `TauCeti.InternalGrading.pieceSubmoduleEquiv`: `k`-linear identification of
  `G.pieceSubmodule 𝒜 p` with `G.piece p`.
* `TauCeti.InternalGrading.positiveSubmodule`: the positive-degree action `A₊ M` as an
  `A₀`-submodule of `M`.
* `TauCeti.InternalGrading.PieceQuotient`: the degree-`p` quotient `(M / A₊ M)ₚ` as an
  `A₀`-module.
* `TauCeti.InternalGrading.pieceQuotientMap`: the `A₀`-linear projection
  `M →ₗ[A₀] G.PieceQuotient 𝒜 p`.

## Main results

* `TauCeti.InternalGrading.pieceQuotientMap_apply`,
  `TauCeti.InternalGrading.pieceQuotientMap_of_mem`,
  `TauCeti.InternalGrading.pieceQuotientMap_of_mem_ne`: evaluation of `pieceQuotientMap` on
  arbitrary and homogeneous elements.
* `TauCeti.InternalGrading.pieceQuotientMap_eq_zero_iff_of_mem`,
  `TauCeti.InternalGrading.pieceQuotientMap_eq_zero`: kernel test for `pieceQuotientMap` on
  degree-`p` elements and elements of `A₊ M`.
* `TauCeti.InternalGrading.pieceQuotientMap_surjective`: surjectivity of `pieceQuotientMap`.
-/

public section

noncomputable section

namespace TauCeti.InternalGrading

open _root_.DirectSum

universe uk uA uM

section Submodules

variable {k : Type uk} [CommSemiring k] {A : Type uA} [Semiring A] [Algebra k A]
  {M : Type uM} [AddCommMonoid M] [Module k M] [Module A M]

/-- The homogeneous piece `G.piece p`, as a module over the degree-zero subalgebra. -/
def pieceSubmodule (G : InternalGrading k M ℤ) (𝒜 : ℤ → Submodule k A)
    [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 G.piece] (p : ℤ) :
    Submodule (SetLike.GradeZero.subalgebra 𝒜) M where
  __ := G.piece p
  smul_mem' c x hx := by
    have hx : x ∈ G.piece p := hx
    rw [Subalgebra.smul_def]
    simpa using SetLike.GradedSMul.smul_mem (A := 𝒜) c.property hx

/-- Membership in `G.pieceSubmodule 𝒜 p` is membership in `G.piece p`. -/
@[simp]
theorem mem_pieceSubmodule {G : InternalGrading k M ℤ} {𝒜 : ℤ → Submodule k A}
    [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 G.piece] {p : ℤ} {x : M} :
    x ∈ G.pieceSubmodule 𝒜 p ↔ x ∈ G.piece p :=
  Iff.rfl

variable [IsScalarTower k A M]

/-- Viewing `G.pieceSubmodule 𝒜 p` over `k` recovers the degree-`p` piece `G.piece p`. -/
def pieceSubmoduleEquiv (G : InternalGrading k M ℤ) (𝒜 : ℤ → Submodule k A)
    [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 G.piece] (p : ℤ) :
    G.pieceSubmodule 𝒜 p ≃ₗ[k] G.piece p where
  toFun x := ⟨x.val, mem_pieceSubmodule.mp x.property⟩
  invFun x := ⟨x.val, mem_pieceSubmodule.mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Applying `pieceSubmoduleEquiv` extracts the element of `G.piece p`. -/
@[simp]
theorem pieceSubmoduleEquiv_apply (G : InternalGrading k M ℤ) (𝒜 : ℤ → Submodule k A)
    [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 G.piece] (p : ℤ)
    (x : G.pieceSubmodule 𝒜 p) :
    G.pieceSubmoduleEquiv 𝒜 p x = ⟨x.val, mem_pieceSubmodule.mp x.property⟩ := by
  rfl

/-- Applying `(G.pieceSubmoduleEquiv 𝒜 p).symm` packages an element of `G.piece p` as a term of
`G.pieceSubmodule 𝒜 p`. -/
@[simp]
theorem pieceSubmoduleEquiv_symm_apply (G : InternalGrading k M ℤ) (𝒜 : ℤ → Submodule k A)
    [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 G.piece] (p : ℤ)
    (x : G.piece p) :
    (G.pieceSubmoduleEquiv 𝒜 p).symm x = ⟨x.val, mem_pieceSubmodule.mpr x.property⟩ := by
  rfl

end Submodules

section PositiveSubmodule

variable {k : Type uk} [CommSemiring k] {A : Type uA} [Semiring A] [Algebra k A]

/-- The positive-degree action `A₊ M`, as a module over the degree-zero subalgebra. -/
def positiveSubmodule (M : Type uM) [AddCommMonoid M] [Module k M] [Module A M]
    [IsScalarTower k A M] (𝒜 : ℤ → Submodule k A) [SetLike.GradedMonoid 𝒜] :
    Submodule (SetLike.GradeZero.subalgebra 𝒜) M where
  __ := (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)
  smul_mem' c x hx := by
    rw [Subalgebra.smul_def]
    exact smul_mem_positive_smul_top c.property hx

/-- Membership in `positiveSubmodule M 𝒜` is membership in `A₊ M`. -/
@[simp]
theorem mem_positiveSubmodule {M : Type uM} [AddCommMonoid M] [Module k M] [Module A M]
    [IsScalarTower k A M] {𝒜 : ℤ → Submodule k A} [SetLike.GradedMonoid 𝒜] {x : M} :
    x ∈ positiveSubmodule M 𝒜 ↔ x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) :=
  Iff.rfl

end PositiveSubmodule

section Quotient

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {M : Type uM} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

/-- The homogeneous piece `(M / A₊ M)ₚ`, as a module over the degree-zero subalgebra. -/
abbrev PieceQuotient (G : InternalGrading k M ℤ) (𝒜 : ℤ → Submodule k A)
    [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 G.piece] (p : ℤ) :=
  G.pieceSubmodule 𝒜 p ⧸ (positiveSubmodule M 𝒜).comap (G.pieceSubmodule 𝒜 p).subtype

/-- Projection to the degree-`p` piece of `M / A₊ M`. -/
def pieceQuotientMap (G : InternalGrading k M ℤ) (𝒜 : ℤ → Submodule k A)
    [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 G.piece] (p : ℤ) :
    M →ₗ[SetLike.GradeZero.subalgebra 𝒜] G.PieceQuotient 𝒜 p :=
  Submodule.mkQ _ ∘ₗ
    { toFun x := ⟨decompose G.piece x p, (decompose G.piece x p).property⟩
      map_add' x y := by ext; simp
      map_smul' c x := by
        ext
        -- Multiplication by a degree-zero scalar is homogeneous of degree zero.
        have hf : LinearMap.IsHomogeneous (Algebra.lsmul k k M (c : A))
            G.piece G.piece 0 :=
          LinearMap.isHomogeneous_def.mpr fun q z hz => by
            simpa [add_comm] using SetLike.GradedSMul.smul_mem (A := 𝒜) c.property hz
        have h := hf.map_decompose p x
        rw [add_zero] at h
        simpa [Subalgebra.smul_def] using h.symm }

/-- `G.pieceQuotientMap 𝒜 p x` is the quotient class of the degree-`p` component of `x`. -/
theorem pieceQuotientMap_apply {G : InternalGrading k M ℤ} {𝒜 : ℤ → Submodule k A}
    [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 G.piece] (p : ℤ) (x : M) :
    G.pieceQuotientMap 𝒜 p x =
      Submodule.Quotient.mk ⟨decompose G.piece x p,
        mem_pieceSubmodule.mpr (decompose G.piece x p).property⟩ := by
  rfl

/-- On a degree-`p` element, `pieceQuotientMap` is the quotient class in `PieceQuotient`. -/
theorem pieceQuotientMap_of_mem {G : InternalGrading k M ℤ} {𝒜 : ℤ → Submodule k A}
    [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 G.piece] {p : ℤ} {x : M}
    (hx : x ∈ G.piece p) :
    G.pieceQuotientMap 𝒜 p x = Submodule.Quotient.mk ⟨x, mem_pieceSubmodule.mpr hx⟩ := by
  simp [pieceQuotientMap_apply, decompose_of_mem_same _ hx]

/-- On an element homogeneous of degree `q ≠ p`, `pieceQuotientMap` vanishes. -/
theorem pieceQuotientMap_of_mem_ne {G : InternalGrading k M ℤ} {𝒜 : ℤ → Submodule k A}
    [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 G.piece] {p q : ℤ} {x : M}
    (hx : x ∈ G.piece q) (hqp : q ≠ p) : G.pieceQuotientMap 𝒜 p x = 0 := by
  simp [pieceQuotientMap_apply, decompose_of_mem_ne _ hx hqp]

/-- A degree-`p` element maps to zero under `pieceQuotientMap` if and only if it lies in `A₊ M`. -/
theorem pieceQuotientMap_eq_zero_iff_of_mem {G : InternalGrading k M ℤ} {𝒜 : ℤ → Submodule k A}
    [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 G.piece] {p : ℤ} {x : M}
    (hx : x ∈ G.piece p) :
    G.pieceQuotientMap 𝒜 p x = 0 ↔
      x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
  rw [pieceQuotientMap_of_mem hx, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    Submodule.coe_subtype, mem_positiveSubmodule]

/-- Elements of `A₊ M` map to zero under `pieceQuotientMap`. -/
theorem pieceQuotientMap_eq_zero {G : InternalGrading k M ℤ} {𝒜 : ℤ → Submodule k A}
    [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 G.piece] {p : ℤ} {x : M}
    (hx : x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) :
    G.pieceQuotientMap 𝒜 p x = 0 := by
  rw [pieceQuotientMap_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    Submodule.coe_subtype, mem_positiveSubmodule]
  exact isHomogeneous_positive_smul_top 𝒜 p hx

/-- The quotient projection `G.pieceQuotientMap 𝒜 p` is surjective. -/
theorem pieceQuotientMap_surjective (G : InternalGrading k M ℤ) (𝒜 : ℤ → Submodule k A)
    [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 G.piece] (p : ℤ) :
    Function.Surjective (G.pieceQuotientMap 𝒜 p) := by
  intro q
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨x, pieceQuotientMap_of_mem (mem_pieceSubmodule.mp hx)⟩

end Quotient

end TauCeti.InternalGrading
