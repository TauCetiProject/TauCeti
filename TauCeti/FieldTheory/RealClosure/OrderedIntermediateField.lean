/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Algebra.Order.Ring.Ordering.Extension
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Hom.Monoid

/-! # Ordered intermediate fields of a field extension

The ambient field need not be ordered. An intermediate field carries its
positive cone, allowing compatible chains of ordered fields to be united.
`OrderedIntermediateField.exists_isMax` supplies the Zorn maximal element, and
`OrderedIntermediateField.mem_of_isMax` shows that ordered extensions embedded in the ambient
field stay inside it. This is the maximality step in the real-closure construction.
-/

public section

namespace TauCeti.RealClosure

variable (K L : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Field L] [Algebra K L]

/-- An ordered intermediate field whose order extends that of the base. -/
@[ext] structure OrderedIntermediateField where
  /-- The underlying intermediate field. -/
  toIntermediateField : IntermediateField K L
  /-- The nonnegative elements, represented in the ambient field. -/
  nonneg : Subsemiring L
  nonneg_subset : ∀ x ∈ nonneg, x ∈ toIntermediateField
  mem_or_neg_mem : ∀ x ∈ toIntermediateField, x ∈ nonneg ∨ -x ∈ nonneg
  neg_one_notMem : -1 ∉ nonneg
  algebraMap_mem_nonneg : ∀ x : K, 0 ≤ x → algebraMap K L x ∈ nonneg

namespace OrderedIntermediateField

variable {K L}

instance : PartialOrder (OrderedIntermediateField K L) :=
  PartialOrder.lift (fun P => (P.toIntermediateField, P.nonneg)) (by
    intro P Q h
    obtain ⟨hf, hn⟩ := Prod.mk.inj h
    exact OrderedIntermediateField.ext hf hn)

omit [IsStrictOrderedRing K] in
theorem le_iff (P Q : OrderedIntermediateField K L) :
    P ≤ Q ↔ P.toIntermediateField ≤ Q.toIntermediateField ∧ P.nonneg ≤ Q.nonneg := Iff.rfl

/-- The positive cone viewed inside its own intermediate field. -/
def preordering (P : OrderedIntermediateField K L) : RingPreordering P.toIntermediateField where
  __ := P.nonneg.comap P.toIntermediateField.val.toRingHom
  mem_of_isSquare' := by
    rintro x ⟨y, rfl⟩
    -- The inherited carrier field is still wrapped by `comap` in this constructor goal;
    -- reducing it exposes ambient membership. `simp [mem_comap, map_mul]` does not unfold it.
    change y.val * y.val ∈ P.nonneg
    rcases P.mem_or_neg_mem y.val y.property with hy | hy
    · exact mul_mem hy hy
    · simpa only [neg_mul_neg] using mul_mem hy hy
  neg_one_notMem' := P.neg_one_notMem

omit [IsStrictOrderedRing K] in
@[simp] theorem mem_preordering (P : OrderedIntermediateField K L) (x : P.toIntermediateField) :
    x ∈ P.preordering ↔ x.val ∈ P.nonneg := (Iff.rfl)

instance (P : OrderedIntermediateField K L) : (preordering P).IsOrdering where
  mem_or_neg_mem x := P.mem_or_neg_mem x.val x.property
  toIsPrime := inferInstance

/-- The induced linear order on the intermediate field. -/
@[instance_reducible] noncomputable def linearOrder (P : OrderedIntermediateField K L) :
    LinearOrder P.toIntermediateField := RingPreordering.linearOrder P.preordering

omit [IsStrictOrderedRing K] in
theorem isStrictOrderedRing (P : OrderedIntermediateField K L) : letI := P.linearOrder
    IsStrictOrderedRing P.toIntermediateField := RingPreordering.isStrictOrderedRing P.preordering

omit [IsStrictOrderedRing K] in
theorem nonneg_iff (P : OrderedIntermediateField K L) (x : P.toIntermediateField) :
    letI := P.linearOrder
    0 ≤ x ↔ x.val ∈ P.nonneg :=
  (RingPreordering.nonneg_iff P.preordering x).trans (P.mem_preordering x)

theorem algebraMap_strictMono (P : OrderedIntermediateField K L) : letI := P.linearOrder
    StrictMono (algebraMap K P.toIntermediateField) := by
  let := P.linearOrder
  have := P.isStrictOrderedRing
  exact ((monotone_iff_map_nonneg (algebraMap K P.toIntermediateField)).mpr fun x hx =>
    (P.nonneg_iff _).mpr (P.algebraMap_mem_nonneg x hx)).strictMono_of_injective
      (algebraMap K P.toIntermediateField).injective

/-- The image of an ordered extension under an embedding into the ambient field. -/
private def image {E : Type*} [Field E] [LinearOrder E] [IsStrictOrderedRing E] [Algebra K E]
    (hf : Monotone (algebraMap K E)) (f : E →ₐ[K] L) : OrderedIntermediateField K L where
  toIntermediateField := f.fieldRange
  nonneg := (Subsemiring.nonneg E).map f.toRingHom
  nonneg_subset := by
    rintro x ⟨y, _, rfl⟩
    exact ⟨y, rfl⟩
  mem_or_neg_mem := by
    rintro x ⟨y, rfl⟩
    rcases le_total 0 y with hy | hy
    · exact Or.inl ⟨y, hy, rfl⟩
    · exact Or.inr ⟨-y, neg_nonneg.mpr hy, map_neg f y⟩
  neg_one_notMem := by
    rintro ⟨y, hy, heq⟩
    have : y = -1 := f.injective (by simpa using heq)
    exact (not_le_of_gt zero_lt_one) (by simpa [this] using hy)
  algebraMap_mem_nonneg x hx := ⟨algebraMap K E x, by simpa using hf hx, f.commutes x⟩

/-- The base field as an ordered intermediate field. -/
private def base : OrderedIntermediateField K L :=
  image (by simpa using monotone_id) (Algebra.ofId K L)

instance : Nonempty (OrderedIntermediateField K L) := ⟨base⟩

/-- The union of a nonempty chain of compatible ordered intermediate fields. -/
private def chainUnion (c : Set (OrderedIntermediateField K L)) (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) : OrderedIntermediateField K L := by
  have := hne.to_subtype
  have hf : Directed (· ≤ ·) (fun P : c => P.val.toIntermediateField) :=
    hc.directed.mono_comp _ (fun _ _ h => h.1)
  have hn : Directed (· ≤ ·) (fun P : c => P.val.nonneg) :=
    hc.directed.mono_comp _ (fun _ _ h => h.2)
  exact
    { toIntermediateField :=
        (⨆ P : c, P.val.toIntermediateField).copy {x | ∃ P ∈ c, x ∈ P.toIntermediateField} (by
        rw [IntermediateField.coe_iSup_of_directed hf]
        ext x
        simp)
      nonneg := (⨆ P : c, P.val.nonneg).copy {x | ∃ P ∈ c, x ∈ P.nonneg} (by
        rw [Subsemiring.coe_iSup_of_directed hn]
        ext x
        simp)
      nonneg_subset := by rintro x ⟨P, hP, hx⟩; exact ⟨P, hP, P.nonneg_subset x hx⟩
      mem_or_neg_mem := by
        rintro x ⟨P, hP, hx⟩
        exact (P.mem_or_neg_mem x hx).imp (fun h => ⟨P, hP, h⟩) (fun h => ⟨P, hP, h⟩)
      neg_one_notMem := by rintro ⟨P, _, hp⟩; exact P.neg_one_notMem hp
      algebraMap_mem_nonneg := by
        intro x hx
        obtain ⟨P, hP⟩ := hne
        exact ⟨P, hP, P.algebraMap_mem_nonneg x hx⟩ }

omit [IsStrictOrderedRing K] in
private theorem le_chainUnion (c : Set (OrderedIntermediateField K L)) (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) {P : OrderedIntermediateField K L} (hP : P ∈ c) :
    P ≤ chainUnion c hc hne :=
  ⟨fun _ hx => ⟨P, hP, hx⟩, fun _ hx => ⟨P, hP, hx⟩⟩

/-- There is a maximal ordered intermediate field extending the given base order. -/
theorem exists_isMax : ∃ P : OrderedIntermediateField K L, IsMax P :=
  zorn_le_nonempty fun c hc hne =>
    ⟨chainUnion c hc hne, fun _ hP => le_chainUnion c hc hne hP⟩

/-- An ordered extension embedded in the ambient field gives a larger ordered
intermediate field, with the original signs preserved. -/
theorem exists_le_mem (P : OrderedIntermediateField K L) {E : Type*}
    [Field E] [LinearOrder E] [IsStrictOrderedRing E] [Algebra K E]
    [Algebra P.toIntermediateField E] [IsScalarTower K P.toIntermediateField E]
    (f : E →ₐ[P.toIntermediateField] L) :
    letI := P.linearOrder
    Monotone (algebraMap P.toIntermediateField E) →
      ∃ Q : OrderedIntermediateField K L, P ≤ Q ∧ ∀ x : E, f x ∈ Q.toIntermediateField := by
  let := P.linearOrder
  have := P.isStrictOrderedRing
  intro hf
  have hbase : Monotone (algebraMap K E) := by
    intro a b hab
    simpa only [← IsScalarTower.algebraMap_apply K P.toIntermediateField E] using
      hf (P.algebraMap_strictMono.monotone hab)
  let Q := image hbase (f.restrictScalars K)
  refine ⟨Q, ⟨?_, ?_⟩, fun x => ⟨x, rfl⟩⟩
  · intro x hx
    exact ⟨algebraMap P.toIntermediateField E ⟨x, hx⟩, f.commutes ⟨x, hx⟩⟩
  · intro x hx
    let y : P.toIntermediateField := ⟨x, P.nonneg_subset x hx⟩
    have hy : 0 ≤ y := (P.nonneg_iff y).mpr hx
    exact ⟨algebraMap P.toIntermediateField E y, by simpa using hf hy, f.commutes y⟩

/-- Every embedding of an ordered extension of a maximal ordered intermediate field `P`
into the ambient field has its image inside `P.toIntermediateField`. -/
theorem mem_of_isMax (P : OrderedIntermediateField K L) (hP : IsMax P) {E : Type*}
    [Field E] [LinearOrder E] [IsStrictOrderedRing E] [Algebra K E]
    [Algebra P.toIntermediateField E] [IsScalarTower K P.toIntermediateField E]
    (f : E →ₐ[P.toIntermediateField] L) :
    letI := P.linearOrder
    Monotone (algebraMap P.toIntermediateField E) → ∀ x : E, f x ∈ P.toIntermediateField := by
  intro hf x
  obtain ⟨Q, hPQ, hQ⟩ := P.exists_le_mem f hf
  exact (hP hPQ).1 (hQ x)

end OrderedIntermediateField

end TauCeti.RealClosure
