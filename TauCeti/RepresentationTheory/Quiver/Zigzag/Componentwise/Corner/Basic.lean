/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Multiplication
public import TauCeti.RingTheory.Idempotents.Corner

/-!
# Corners of the componentwise zigzag algebra

For distinct nonadjacent vertices `i, j` of a finite simple graph, the corner
`e_i Z e_j` of the componentwise zigzag algebra is zero, including when either
vertex is isolated. These corners enter the calculation of tensor products
of the vertex projective bimodules. The diagonal corner is spanned by
the vertex and its volume vector; its coordinates give the two middle
summands in the self-tensor calculation used for inverse braid complexes.

See Huerfano--Khovanov, *A category for the adjoint representation*.
-/

public section

namespace TauCeti

variable (k : Type*) [CommRing k] {V : Type*} (G : SimpleGraph V) [Finite V]

local notation "e" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inl i)

/-- Each vertex basis element of the componentwise zigzag algebra is idempotent. -/
theorem isIdempotentElem_zigzagAlgebraBasis_inl (i : V) :
    IsIdempotentElem (zigzagAlgebraBasis k G (Sum.inl i)) := by
  simp [IsIdempotentElem]

/-- Distinct nonadjacent vertex idempotents cut out a zero corner of the public
zigzag algebra, including its isolated-vertex dual-number factors. -/
theorem cornerSubmodule_zigzagAlgebra_eq_bot_of_ne_of_not_adj {i j : V}
    (hij : i ≠ j) (hadj : ¬ G.Adj i j) : cornerSubmodule k (e i) (e j) = ⊥ := by
  classical
  have hzero : LinearMap.mulLeftRight k (e i, e j) = 0 := by
    apply (zigzagAlgebraBasis k G).ext
    intro b
    simp only [LinearMap.mulLeftRight_apply, LinearMap.zero_apply]
    rcases b with v | d | v
    · by_cases h : i = v
      · subst v
        simp [hij]
      · simp [h]
    · by_cases h : i = d.snd
      · by_cases h' : d.fst = j
        · have ha : G.Adj i j := by simpa only [h, ← h'] using d.adj.symm
          exact (hadj ha).elim
        · simp [h, Ne.symm h']
      · simp [h]
    · by_cases h : i = v
      · subst v
        simp [hij]
      · simp [h]
  rw [cornerSubmodule_def]
  exact LinearMap.range_eq_bot.mpr hzero

/-- Distinct nonadjacent vertex idempotents kill every algebra element between them. -/
theorem zigzagAlgebraBasis_inl_mul_mul_eq_zero_of_ne_of_not_adj {i j : V}
    (hij : i ≠ j) (hadj : ¬ G.Adj i j) (x : zigzagAlgebra k G) :
    e i * x * e j = 0 := by
  have h := mul_mul_mem_cornerSubmodule k (e i) (e j) x
  simpa only [cornerSubmodule_zigzagAlgebra_eq_bot_of_ne_of_not_adj k G hij hadj,
    Submodule.mem_bot] using h

/-- Cutting down at the same vertex keeps exactly the vertex and volume coordinates. -/
theorem zigzagAlgebraBasis_inl_mul_mul_self (i : V) (x : zigzagAlgebra k G) :
    e i * x * e i =
      (zigzagAlgebraBasis k G).repr x (.inl i) • e i +
        (zigzagAlgebraBasis k G).repr x (.inr (.inr i)) •
          zigzagAlgebraBasis k G (.inr (.inr i)) := by
  classical
  have key : LinearMap.mulLeftRight k (e i, e i) =
      ((zigzagAlgebraBasis k G).coord (.inl i)).smulRight (e i) +
        ((zigzagAlgebraBasis k G).coord (.inr (.inr i))).smulRight
          (zigzagAlgebraBasis k G (.inr (.inr i))) := by
    apply (zigzagAlgebraBasis k G).ext
    intro b
    simp only [LinearMap.mulLeftRight_apply, LinearMap.add_apply,
      LinearMap.smulRight_apply, Module.Basis.coord_apply, Module.Basis.repr_self]
    rcases b with j | d | j
    · by_cases h : i = j
      · subst j
        simp
      · simp [h]
    · by_cases h : i = d.snd
      · simp [h]
      · simp [h]
    · by_cases h : i = j
      · subst j
        simp
      · simp [h]
  exact LinearMap.congr_fun key x

/-- The diagonal corner consists of the span of the vertex and volume basis vectors. -/
theorem cornerSubmodule_zigzagAlgebra_self_eq_span (i : V) :
    cornerSubmodule k (e i) (e i) =
      Submodule.span k {e i, zigzagAlgebraBasis k G (.inr (.inr i))} := by
  apply le_antisymm
  · intro x hx
    have h := (mem_cornerSubmodule_iff k (isIdempotentElem_zigzagAlgebraBasis_inl k G i)
      (isIdempotentElem_zigzagAlgebraBasis_inl k G i)).mp hx
    rw [← h, zigzagAlgebraBasis_inl_mul_mul_self]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · rw [Submodule.span_le]
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact (mem_cornerSubmodule_iff k (isIdempotentElem_zigzagAlgebraBasis_inl k G i)
        (isIdempotentElem_zigzagAlgebraBasis_inl k G i)).mpr (by simp)
    · have hx' : x = zigzagAlgebraBasis k G (.inr (.inr i)) := Set.mem_singleton_iff.mp hx
      subst x
      exact (mem_cornerSubmodule_iff k (isIdempotentElem_zigzagAlgebraBasis_inl k G i)
        (isIdempotentElem_zigzagAlgebraBasis_inl k G i)).mpr (by simp)

/-- The vertex and volume coordinates identify the diagonal corner with two ground-ring copies. -/
noncomputable def zigzagAlgebraSelfCornerEquiv (i : V) :
    cornerSubmodule k (e i) (e i) ≃ₗ[k] k × k where
  toFun x := ((zigzagAlgebraBasis k G).repr x (.inl i),
    (zigzagAlgebraBasis k G).repr x (.inr (.inr i)))
  invFun a := ⟨a.1 • e i + a.2 • zigzagAlgebraBasis k G (.inr (.inr i)), by
    rw [cornerSubmodule_zigzagAlgebra_self_eq_span]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))⟩
  map_add' x y := by simp
  map_smul' r x := by simp
  left_inv x := Subtype.ext <|
    (zigzagAlgebraBasis_inl_mul_mul_self k G i x).symm.trans
      ((mem_cornerSubmodule_iff k (isIdempotentElem_zigzagAlgebraBasis_inl k G i)
        (isIdempotentElem_zigzagAlgebraBasis_inl k G i)).mp x.2)
  right_inv a := by simp

@[simp]
theorem zigzagAlgebraSelfCornerEquiv_apply (i : V)
    (x : cornerSubmodule k (e i) (e i)) :
    zigzagAlgebraSelfCornerEquiv k G i x =
      ((zigzagAlgebraBasis k G).repr x (.inl i),
        (zigzagAlgebraBasis k G).repr x (.inr (.inr i))) := (rfl)

@[simp]
theorem coe_zigzagAlgebraSelfCornerEquiv_symm_apply (i : V) (a : k × k) :
    ((zigzagAlgebraSelfCornerEquiv k G i).symm a : zigzagAlgebra k G) =
      a.1 • e i + a.2 • zigzagAlgebraBasis k G (.inr (.inr i)) := (rfl)

end TauCeti
