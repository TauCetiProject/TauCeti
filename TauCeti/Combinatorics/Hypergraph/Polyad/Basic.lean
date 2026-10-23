/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Regular
public import Mathlib.Data.Matrix.Basic

/-!
# Triadic polyads

A `Polyad3` records three vertex cells of a lower skeleton and one pair color for each of the
three canonically oriented role pairs. Its support is computed from this data: it consists of the
role-ordered injective triples in the chosen cells whose coordinate pairs have the chosen colors.
Thus a polyad carries no independently chosen support.

The three pair supports expose the colored bigraphs whose arbitrary subgraphs form subpolyads.
The `faceKey` convention translates colors indexed by role pairs to the omitted-coordinate
indexing used by face-based descriptions of triads.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*.
* B. Nagle, V. Rödl and M. Schacht, *The counting lemma for regular k-uniform hypergraphs*.
-/

public section

open Finset

namespace TauCeti

variable {κ V : Type*} [Fintype V] [DecidableEq V]

/-- A triadic polyad over a lower skeleton: three vertex cells and the colors of the three
canonically oriented pairs of roles. Its support is derived from these six data fields. -/
structure Polyad3 (S : PairSkeleton3 κ V) where
  /-- The vertex cell at role zero. -/
  c₀ : Finset V
  /-- The vertex cell at role one. -/
  c₁ : Finset V
  /-- The vertex cell at role two. -/
  c₂ : Finset V
  /-- The role-zero cell belongs to the skeleton partition. -/
  hc₀ : c₀ ∈ S.vertexPart.parts
  /-- The role-one cell belongs to the skeleton partition. -/
  hc₁ : c₁ ∈ S.vertexPart.parts
  /-- The role-two cell belongs to the skeleton partition. -/
  hc₂ : c₂ ∈ S.vertexPart.parts
  /-- The color on the ordered role pair `(0, 1)`. -/
  color₀₁ : κ
  /-- The color on the ordered role pair `(0, 2)`. -/
  color₀₂ : κ
  /-- The color on the ordered role pair `(1, 2)`. -/
  color₁₂ : κ

/-- The injective triples in specified cells whose three canonically oriented coordinate pairs
have the specified colors. -/
noncomputable def polyadSupport (C : PairColorSystem κ V) (c₀ c₁ c₂ : Finset V)
    (k₀₁ k₀₂ k₁₂ : κ) : Finset {x : Fin 3 → V // Function.Injective x} := by
  classical
  exact univ.filter fun x ↦
    x.1 0 ∈ c₀ ∧ x.1 1 ∈ c₁ ∧ x.1 2 ∈ c₂ ∧
      C.colorOfPair (x.1 0) (x.1 1) = some k₀₁ ∧
      C.colorOfPair (x.1 0) (x.1 2) = some k₀₂ ∧
      C.colorOfPair (x.1 1) (x.1 2) = some k₁₂

/-- Membership in a computed polyad support. -/
@[simp]
theorem mem_polyadSupport {C : PairColorSystem κ V} {c₀ c₁ c₂ : Finset V}
    {k₀₁ k₀₂ k₁₂ : κ} {x : {x : Fin 3 → V // Function.Injective x}} :
    x ∈ polyadSupport C c₀ c₁ c₂ k₀₁ k₀₂ k₁₂ ↔
      x.1 0 ∈ c₀ ∧ x.1 1 ∈ c₁ ∧ x.1 2 ∈ c₂ ∧
        C.colorOfPair (x.1 0) (x.1 1) = some k₀₁ ∧
        C.colorOfPair (x.1 0) (x.1 2) = some k₀₂ ∧
        C.colorOfPair (x.1 1) (x.1 2) = some k₁₂ := by
  simp [polyadSupport]

namespace Polyad3

variable {S : PairSkeleton3 κ V}

/-- The support of a polyad, computed from its cells and pair colors. -/
noncomputable def support (P : Polyad3 S) :
    Finset {x : Fin 3 → V // Function.Injective x} :=
  polyadSupport S.pairColors P.c₀ P.c₁ P.c₂ P.color₀₁ P.color₀₂ P.color₁₂

/-- Membership in a polyad's computed support. -/
@[simp]
theorem mem_support (P : Polyad3 S) (x : {x : Fin 3 → V // Function.Injective x}) :
    x ∈ P.support ↔
      x.1 0 ∈ P.c₀ ∧ x.1 1 ∈ P.c₁ ∧ x.1 2 ∈ P.c₂ ∧
        S.pairColors.colorOfPair (x.1 0) (x.1 1) = some P.color₀₁ ∧
        S.pairColors.colorOfPair (x.1 0) (x.1 2) = some P.color₀₂ ∧
        S.pairColors.colorOfPair (x.1 1) (x.1 2) = some P.color₁₂ :=
  mem_polyadSupport

/-- Two polyads are equal when their three cells and three pair colors agree. -/
@[ext]
theorem ext_data {P Q : Polyad3 S} (h₀ : P.c₀ = Q.c₀) (h₁ : P.c₁ = Q.c₁)
    (h₂ : P.c₂ = Q.c₂) (hk₀₁ : P.color₀₁ = Q.color₀₁)
    (hk₀₂ : P.color₀₂ = Q.color₀₂) (hk₁₂ : P.color₁₂ = Q.color₁₂) : P = Q := by
  cases P
  cases Q
  simp only at h₀ h₁ h₂ hk₀₁ hk₀₂ hk₁₂
  subst h₀
  subst h₁
  subst h₂
  subst hk₀₁
  subst hk₀₂
  subst hk₁₂
  rfl

/-- The six data fields of a polyad, with its cells bundled as parts of the skeleton. -/
private def partData (P : Polyad3 S) :
    (S.vertexPart.parts × S.vertexPart.parts × S.vertexPart.parts) × κ × κ × κ :=
  ((⟨P.c₀, P.hc₀⟩, ⟨P.c₁, P.hc₁⟩, ⟨P.c₂, P.hc₂⟩),
    P.color₀₁, P.color₀₂, P.color₁₂)

/-- The data encoding of polyads is injective. -/
private theorem partData_injective : Function.Injective (partData (S := S)) := by
  intro P Q h
  simp only [partData, Prod.mk.injEq, Subtype.mk.injEq] at h
  exact ext_data h.1.1 h.1.2.1 h.1.2.2 h.2.1 h.2.2.1 h.2.2.2

/-- Polyads have decidable equality when the pair palette does. -/
@[no_expose] noncomputable instance [DecidableEq κ] : DecidableEq (Polyad3 S) :=
  partData_injective.decidableEq

/-- There are finitely many polyads over a finite pair palette. -/
@[no_expose] noncomputable instance [Fintype κ] : Fintype (Polyad3 S) :=
  Fintype.ofInjective _ partData_injective

/-- The polyad determined by three cells of the skeleton and three pair colors. -/
def ofData (c₀ c₁ c₂ : Finset V) (h₀ : c₀ ∈ S.vertexPart.parts)
    (h₁ : c₁ ∈ S.vertexPart.parts) (h₂ : c₂ ∈ S.vertexPart.parts)
    (k₀₁ k₀₂ k₁₂ : κ) : Polyad3 S where
  c₀ := c₀
  c₁ := c₁
  c₂ := c₂
  hc₀ := h₀
  hc₁ := h₁
  hc₂ := h₂
  color₀₁ := k₀₁
  color₀₂ := k₀₂
  color₁₂ := k₁₂

/-- The role-zero cell of `ofData` is the given one. -/
@[simp]
theorem ofData_c₀ (c₀ c₁ c₂ : Finset V) (h₀ : c₀ ∈ S.vertexPart.parts)
    (h₁ : c₁ ∈ S.vertexPart.parts) (h₂ : c₂ ∈ S.vertexPart.parts) (k₀₁ k₀₂ k₁₂ : κ) :
    (ofData c₀ c₁ c₂ h₀ h₁ h₂ k₀₁ k₀₂ k₁₂).c₀ = c₀ := (rfl)

/-- The role-one cell of `ofData` is the given one. -/
@[simp]
theorem ofData_c₁ (c₀ c₁ c₂ : Finset V) (h₀ : c₀ ∈ S.vertexPart.parts)
    (h₁ : c₁ ∈ S.vertexPart.parts) (h₂ : c₂ ∈ S.vertexPart.parts) (k₀₁ k₀₂ k₁₂ : κ) :
    (ofData c₀ c₁ c₂ h₀ h₁ h₂ k₀₁ k₀₂ k₁₂).c₁ = c₁ := (rfl)

/-- The role-two cell of `ofData` is the given one. -/
@[simp]
theorem ofData_c₂ (c₀ c₁ c₂ : Finset V) (h₀ : c₀ ∈ S.vertexPart.parts)
    (h₁ : c₁ ∈ S.vertexPart.parts) (h₂ : c₂ ∈ S.vertexPart.parts) (k₀₁ k₀₂ k₁₂ : κ) :
    (ofData c₀ c₁ c₂ h₀ h₁ h₂ k₀₁ k₀₂ k₁₂).c₂ = c₂ := (rfl)

/-- The color on roles zero and one of `ofData` is the given one. -/
@[simp]
theorem ofData_color₀₁ (c₀ c₁ c₂ : Finset V) (h₀ : c₀ ∈ S.vertexPart.parts)
    (h₁ : c₁ ∈ S.vertexPart.parts) (h₂ : c₂ ∈ S.vertexPart.parts) (k₀₁ k₀₂ k₁₂ : κ) :
    (ofData c₀ c₁ c₂ h₀ h₁ h₂ k₀₁ k₀₂ k₁₂).color₀₁ = k₀₁ := (rfl)

/-- The color on roles zero and two of `ofData` is the given one. -/
@[simp]
theorem ofData_color₀₂ (c₀ c₁ c₂ : Finset V) (h₀ : c₀ ∈ S.vertexPart.parts)
    (h₁ : c₁ ∈ S.vertexPart.parts) (h₂ : c₂ ∈ S.vertexPart.parts) (k₀₁ k₀₂ k₁₂ : κ) :
    (ofData c₀ c₁ c₂ h₀ h₁ h₂ k₀₁ k₀₂ k₁₂).color₀₂ = k₀₂ := (rfl)

/-- The color on roles one and two of `ofData` is the given one. -/
@[simp]
theorem ofData_color₁₂ (c₀ c₁ c₂ : Finset V) (h₀ : c₀ ∈ S.vertexPart.parts)
    (h₁ : c₁ ∈ S.vertexPart.parts) (h₂ : c₂ ∈ S.vertexPart.parts) (k₀₁ k₀₂ k₁₂ : κ) :
    (ofData c₀ c₁ c₂ h₀ h₁ h₂ k₀₁ k₀₂ k₁₂).color₁₂ = k₁₂ := (rfl)

/-- The pair graph of a polyad on roles zero and one. -/
noncomputable def pairSupport₀₁ (P : Polyad3 S) :
    Finset {p : V × V // p.1 ≠ p.2} := by
  classical
  exact univ.filter fun p ↦
    p.1.1 ∈ P.c₀ ∧ p.1.2 ∈ P.c₁ ∧ S.pairColors.color p = P.color₀₁

/-- The pair graph of a polyad on roles zero and two. -/
noncomputable def pairSupport₀₂ (P : Polyad3 S) :
    Finset {p : V × V // p.1 ≠ p.2} := by
  classical
  exact univ.filter fun p ↦
    p.1.1 ∈ P.c₀ ∧ p.1.2 ∈ P.c₂ ∧ S.pairColors.color p = P.color₀₂

/-- The pair graph of a polyad on roles one and two. -/
noncomputable def pairSupport₁₂ (P : Polyad3 S) :
    Finset {p : V × V // p.1 ≠ p.2} := by
  classical
  exact univ.filter fun p ↦
    p.1.1 ∈ P.c₁ ∧ p.1.2 ∈ P.c₂ ∧ S.pairColors.color p = P.color₁₂

/-- Membership in the pair support on roles zero and one: the pair has its endpoints in the
corresponding cells and carries the corresponding color. -/
@[simp]
theorem mem_pairSupport₀₁ (P : Polyad3 S) (p : {p : V × V // p.1 ≠ p.2}) :
    p ∈ P.pairSupport₀₁ ↔
      p.1.1 ∈ P.c₀ ∧ p.1.2 ∈ P.c₁ ∧ S.pairColors.color p = P.color₀₁ := by
  simp [pairSupport₀₁]

/-- Membership in the pair support on roles zero and two: the pair has its endpoints in the
corresponding cells and carries the corresponding color. -/
@[simp]
theorem mem_pairSupport₀₂ (P : Polyad3 S) (p : {p : V × V // p.1 ≠ p.2}) :
    p ∈ P.pairSupport₀₂ ↔
      p.1.1 ∈ P.c₀ ∧ p.1.2 ∈ P.c₂ ∧ S.pairColors.color p = P.color₀₂ := by
  simp [pairSupport₀₂]

/-- Membership in the pair support on roles one and two: the pair has its endpoints in the
corresponding cells and carries the corresponding color. -/
@[simp]
theorem mem_pairSupport₁₂ (P : Polyad3 S) (p : {p : V × V // p.1 ≠ p.2}) :
    p ∈ P.pairSupport₁₂ ↔
      p.1.1 ∈ P.c₁ ∧ p.1.2 ∈ P.c₂ ∧ S.pairColors.color p = P.color₁₂ := by
  simp [pairSupport₁₂]

end Polyad3

/-- The number of polyads is bounded by the number of choices of three vertex cells and three
pair colors. -/
theorem card_polyad3_le (S : PairSkeleton3 κ V) [Fintype κ] :
    Fintype.card (Polyad3 S) ≤ #S.vertexPart.parts ^ 3 * Fintype.card κ ^ 3 := by
  have h := Fintype.card_le_of_injective _ (Polyad3.partData_injective (S := S))
  simp only [Fintype.card_prod, Fintype.card_coe] at h
  calc
    Fintype.card (Polyad3 S) ≤
        #S.vertexPart.parts * (#S.vertexPart.parts * #S.vertexPart.parts) *
          (Fintype.card κ * (Fintype.card κ * Fintype.card κ)) := h
    _ = #S.vertexPart.parts ^ 3 * Fintype.card κ ^ 3 := by
      simp only [pow_succ, pow_zero]
      ac_rfl

/-- Translate role-pair colors to the face-key convention indexed by the omitted coordinate. -/
def faceKey (k₀₁ k₀₂ k₁₂ : κ) : Fin 3 → κ := ![k₁₂, k₀₂, k₀₁]

@[simp]
theorem faceKey_zero (k₀₁ k₀₂ k₁₂ : κ) : faceKey k₀₁ k₀₂ k₁₂ 0 = k₁₂ := (rfl)

@[simp]
theorem faceKey_one (k₀₁ k₀₂ k₁₂ : κ) : faceKey k₀₁ k₀₂ k₁₂ 1 = k₀₂ := (rfl)

@[simp]
theorem faceKey_two (k₀₁ k₀₂ k₁₂ : κ) : faceKey k₀₁ k₀₂ k₁₂ 2 = k₀₁ := (rfl)

/-- The `(0, 1)` coordinate pair of a supported triple lies in the corresponding pair support. -/
theorem coordPair_mem_pairSupport₀₁ {S : PairSkeleton3 κ V} {P : Polyad3 S}
    {x : {x : Fin 3 → V // Function.Injective x}} (hx : x ∈ P.support) :
    coordPair x 0 1 (by decide) ∈ P.pairSupport₀₁ := by
  rw [P.mem_support] at hx
  obtain ⟨h₀, h₁, -, hk, -, -⟩ := hx
  rw [P.mem_pairSupport₀₁, coe_coordPair]
  exact ⟨h₀, h₁, (S.pairColors.color_coordPair_eq_iff _).2 hk⟩

/-- The `(0, 2)` coordinate pair of a supported triple lies in the corresponding pair support. -/
theorem coordPair_mem_pairSupport₀₂ {S : PairSkeleton3 κ V} {P : Polyad3 S}
    {x : {x : Fin 3 → V // Function.Injective x}} (hx : x ∈ P.support) :
    coordPair x 0 2 (by decide) ∈ P.pairSupport₀₂ := by
  rw [P.mem_support] at hx
  obtain ⟨h₀, -, h₂, -, hk, -⟩ := hx
  rw [P.mem_pairSupport₀₂, coe_coordPair]
  exact ⟨h₀, h₂, (S.pairColors.color_coordPair_eq_iff _).2 hk⟩

/-- The `(1, 2)` coordinate pair of a supported triple lies in the corresponding pair support. -/
theorem coordPair_mem_pairSupport₁₂ {S : PairSkeleton3 κ V} {P : Polyad3 S}
    {x : {x : Fin 3 → V // Function.Injective x}} (hx : x ∈ P.support) :
    coordPair x 1 2 (by decide) ∈ P.pairSupport₁₂ := by
  rw [P.mem_support] at hx
  obtain ⟨-, h₁, h₂, -, -, hk⟩ := hx
  rw [P.mem_pairSupport₁₂, coe_coordPair]
  exact ⟨h₁, h₂, (S.pairColors.color_coordPair_eq_iff _).2 hk⟩

/-- A triple lies in the support of a polyad exactly when its three canonically oriented
coordinate pairs lie in the corresponding pair supports. -/
theorem Polyad3.mem_support_iff_coordPair_mem {S : PairSkeleton3 κ V} {P : Polyad3 S}
    {x : {x : Fin 3 → V // Function.Injective x}} :
    x ∈ P.support ↔ coordPair x 0 1 (by decide) ∈ P.pairSupport₀₁ ∧
      coordPair x 0 2 (by decide) ∈ P.pairSupport₀₂ ∧
        coordPair x 1 2 (by decide) ∈ P.pairSupport₁₂ := by
  refine ⟨fun hx ↦ ⟨coordPair_mem_pairSupport₀₁ hx, coordPair_mem_pairSupport₀₂ hx,
    coordPair_mem_pairSupport₁₂ hx⟩, fun ⟨h₀₁, h₀₂, h₁₂⟩ ↦ ?_⟩
  simp only [P.mem_pairSupport₀₁, P.mem_pairSupport₀₂, P.mem_pairSupport₁₂, coe_coordPair,
    S.pairColors.color_coordPair_eq_iff] at h₀₁ h₀₂ h₁₂
  exact (P.mem_support x).2 ⟨h₀₁.1, h₀₁.2.1, h₀₂.2.1, h₀₁.2.2, h₀₂.2.2, h₁₂.2.2⟩

end TauCeti
