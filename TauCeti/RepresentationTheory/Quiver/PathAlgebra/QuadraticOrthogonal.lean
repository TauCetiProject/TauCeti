/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.QuadraticDual
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Truncation

/-!
# Double orthogonals of quadratic path relations

Over a field and a finite quiver with finite arrow sets, the degree-two part of the path algebra
is finite-dimensional. The path-basis pairing restricts to its standard nondegenerate symmetric
form. Thus taking the quadratic orthogonal complement twice recovers a relation space contained
in degree two. This is the linear-algebra step needed when reversing a quadratic presentation.
-/

public section

namespace TauCeti.PathAlgebra

open _root_.Quiver

universe u v w

variable (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q] [Finite Q]
  [∀ i j : Q, Finite (i ⟶ j)]

private instance : Finite {x : Quiver.TotalPath Q // x.2.2.length = 2} := by
  let f : {x : Quiver.TotalPath Q // x.2.2.length = 2} → ShortPath Q 3 :=
    fun x => ⟨x.1, by omega⟩
  exact Finite.of_injective f (by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : ShortPath Q 3 => z.1) h)

private instance : FiniteDimensional k (grade k Q 2) :=
  Module.Finite.of_basis (gradeBasis k Q 2)

/-- The path-basis pairing restricted to the quadratic part of a finite quiver path algebra. -/
private noncomputable def gradeTwoPairing : LinearMap.BilinForm k (grade k Q 2) :=
  (pathPairing k Q).comp (grade k Q 2).subtype |>.compl₂ (grade k Q 2).subtype

omit [Finite Q] [∀ i j : Q, Finite (i ⟶ j)] in
private theorem gradeTwoPairing_apply (x y : grade k Q 2) :
    gradeTwoPairing k Q x y = pathPairing k Q x.1 y.1 := rfl

omit [Finite Q] [∀ i j : Q, Finite (i ⟶ j)] in
private theorem gradeTwoPairing_basis_self (x : {p : Quiver.TotalPath Q // p.2.2.length = 2}) :
    gradeTwoPairing k Q (gradeBasis k Q 2 x) (gradeBasis k Q 2 x) = 1 := by
  classical
  rw [gradeTwoPairing_apply, coe_gradeBasis_apply,
    pathPairing_apply_ofPath, ofPath_eq_single, pathAlgebraBasis_repr_single]
  simp

omit [Finite Q] [∀ i j : Q, Finite (i ⟶ j)] in
private theorem gradeTwoPairing_basis_ne
    {x y : {p : Quiver.TotalPath Q // p.2.2.length = 2}} (h : x ≠ y) :
    gradeTwoPairing k Q (gradeBasis k Q 2 x) (gradeBasis k Q 2 y) = 0 := by
  classical
  rw [gradeTwoPairing_apply, coe_gradeBasis_apply, coe_gradeBasis_apply,
    pathPairing_apply_ofPath, ofPath_eq_single, pathAlgebraBasis_repr_single]
  exact Finsupp.single_eq_of_ne (fun e => h (Subtype.ext e.symm))

omit [Finite Q] [∀ i j : Q, Finite (i ⟶ j)] in
private theorem gradeTwoPairing_nondegenerate : (gradeTwoPairing k Q).Nondegenerate := by
  classical
  have horth : (gradeTwoPairing k Q).iIsOrtho (gradeBasis k Q 2) := by
    intro i j hij
    exact gradeTwoPairing_basis_ne k Q hij
  apply (horth.nondegenerate_iff_not_isOrtho_basis_self _ _).2
  intro i
  rw [gradeTwoPairing_basis_self]
  exact one_ne_zero

omit [Finite Q] [∀ i j : Q, Finite (i ⟶ j)] in
private theorem gradeTwoPairing_isSymm : (gradeTwoPairing k Q).IsSymm := by
  classical
  apply (LinearMap.BilinForm.isSymm_iff_basis (gradeBasis k Q 2)).2
  intro i j
  by_cases h : i = j
  · subst j
    rfl
  · rw [gradeTwoPairing_basis_ne k Q h,
      gradeTwoPairing_basis_ne k Q (Ne.symm h)]

/-- **Quadratic orthogonal complementation is involutive** for a finite quiver over a field.
The relation space must be contained in degree two; the ambient path algebra itself need not be
finite-dimensional. -/
theorem quadraticOrthogonal_quadraticOrthogonal (R : Submodule k (pathAlgebra k Q))
    (hR : R ≤ grade k Q 2) :
    quadraticOrthogonal k Q (quadraticOrthogonal k Q R) = R := by
  let E := grade k Q 2
  let B := gradeTwoPairing k Q
  let S := R.comap E.subtype
  have horth (T : Submodule k (pathAlgebra k Q)) (hT : T ≤ E) :
      quadraticOrthogonal k Q T =
        (B.orthogonal (T.comap E.subtype)).map E.subtype := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxE, hxorth⟩ := mem_quadraticOrthogonal_iff.mp hx
      refine ⟨⟨x, hxE⟩, ?_, rfl⟩
      apply (LinearMap.BilinForm.mem_orthogonal_iff).2
      intro y hy
      calc
        gradeTwoPairing k Q y ⟨x, hxE⟩ = gradeTwoPairing k Q ⟨x, hxE⟩ y :=
          (gradeTwoPairing_isSymm k Q).eq _ _
        _ = pathPairing k Q x y.1 := gradeTwoPairing_apply k Q _ _
        _ = 0 := hxorth y.1 hy
    · rintro ⟨y, hy, rfl⟩
      rw [mem_quadraticOrthogonal_iff]
      refine ⟨y.2, ?_⟩
      intro z hz
      have hzE : z ∈ E := hT hz
      have hzorth := (LinearMap.BilinForm.mem_orthogonal_iff.mp hy) ⟨z, hzE⟩ hz
      calc
        pathPairing k Q y.1 z = gradeTwoPairing k Q y ⟨z, hzE⟩ :=
          (gradeTwoPairing_apply k Q y ⟨z, hzE⟩).symm
        _ = gradeTwoPairing k Q ⟨z, hzE⟩ y := (gradeTwoPairing_isSymm k Q).eq _ _
        _ = 0 := hzorth
  have h1 := horth R hR
  have h2 := horth (quadraticOrthogonal k Q R)
    (quadraticOrthogonal_le_grade_two _)
  rw [h2, h1, Submodule.comap_map_eq_of_injective E.subtype_injective]
  rw [B.orthogonal_orthogonal (gradeTwoPairing_nondegenerate k Q)
    (gradeTwoPairing_isSymm k Q).isRefl]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hR hx⟩, hx, rfl⟩

end TauCeti.PathAlgebra
