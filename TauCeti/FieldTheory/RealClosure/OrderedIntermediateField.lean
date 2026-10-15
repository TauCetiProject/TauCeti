/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Algebra.Order.Ring.Ordering.Extension
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Algebra
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

variable (K L : Type*) [Field K] [LinearOrder K] [IsOrderedRing K]
    [Field L] [Algebra K L]

/-- An ordered intermediate field whose order extends that of the base. -/
@[ext] structure OrderedIntermediateField extends IntermediateField K L where
  /-- The nonnegative elements, represented in the ambient field. -/
  nonneg : Subsemiring L
  nonneg_subset : ∀ x ∈ nonneg, x ∈ toIntermediateField
  mem_or_neg_mem : ∀ x ∈ toIntermediateField, x ∈ nonneg ∨ -x ∈ nonneg
  neg_one_notMem : -1 ∉ nonneg
  algebraMap_mem_nonneg : ∀ x : K, 0 ≤ x → algebraMap K L x ∈ nonneg

namespace OrderedIntermediateField

variable {K L}

/-- Build an ordered intermediate field from an ordered field embedding and its image. -/
private def ofEmbedding {E : Type*} [Field E] [LinearOrder E] [IsOrderedRing E]
    [Algebra K E] [IsOrderedModule K E] (F : IntermediateField K L) (f : E →ₐ[K] L)
    (hinj : Function.Injective f) (hF : ∀ x : L, x ∈ F ↔ ∃ y : E, f y = x) :
    OrderedIntermediateField K L where
  toIntermediateField := F
  nonneg := (Subsemiring.nonneg E).map f.toRingHom
  nonneg_subset := by
    rintro x ⟨y, _, rfl⟩
    exact (hF _).2 ⟨y, rfl⟩
  mem_or_neg_mem := by
    intro x hx
    obtain ⟨y, rfl⟩ := (hF _).1 hx
    rcases le_total 0 y with hy | hy
    · exact Or.inl ⟨y, hy, rfl⟩
    · exact Or.inr ⟨-y, neg_nonneg.mpr hy, map_neg f y⟩
  neg_one_notMem := by
    rintro ⟨y, hy, heq⟩
    have : y = -1 := hinj (by simpa using heq)
    exact (not_le_of_gt zero_lt_one) (by simpa [this] using hy)
  algebraMap_mem_nonneg x hx :=
    ⟨algebraMap K E x, by simpa using algebraMap_mono E hx, f.commutes x⟩

/-- An equivalent characterization of `OrderedIntermediateField`.
For `F : IntermediateField K L`, this constructor makes `F` into an `OrderedIntermediateField K L`
if the linear order on `F` is compatible with its ring structure and restricts to the linear order
on `K`. This can be seen to be equivalent because the order, ordered-ring structure, and
ordered-module structure on `F` are recovered from the corresponding instances. -/
def ofIntermediateField (F : IntermediateField K L) [LinearOrder F] [IsOrderedRing F]
    [IsOrderedModule K F] : OrderedIntermediateField K L := by
  let f : F →ₐ[K] L := (Algebra.ofId F L).restrictScalars K
  exact ofEmbedding F f f.injective (by
    intro x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.property)

/-- An element of `F` is nonnegative in `ofIntermediateField F` exactly when it is
nonnegative in `F`. -/
@[simp] theorem mem_nonneg_ofIntermediateField (F : IntermediateField K L) [LinearOrder F]
    [IsOrderedRing F] [IsOrderedModule K F] (x : F) :
    (x : L) ∈ (ofIntermediateField F).nonneg ↔ 0 ≤ x := by
  simp [ofIntermediateField, ofEmbedding]

/-- The image of an ordered extension under an embedding into the ambient field. -/
private def image {E : Type*} [Field E] [LinearOrder E] [IsOrderedRing E] [Algebra K E]
    [IsOrderedModule K E] (f : E →ₐ[K] L) : OrderedIntermediateField K L :=
  ofEmbedding f.fieldRange f f.injective (by
    intro x
    rw [f.mem_fieldRange])

/-- The underlying intermediate field of `ofIntermediateField F` is `F`. -/
@[simp] theorem toIntermediateField_ofIntermediateField (F : IntermediateField K L)
    [LinearOrder F] [IsOrderedRing F] [IsOrderedModule K F] :
    (ofIntermediateField F).toIntermediateField = F := (rfl)

instance : PartialOrder (OrderedIntermediateField K L) :=
  PartialOrder.lift (fun P => (P.toIntermediateField, P.nonneg)) (by
    intro P Q h
    obtain ⟨hf, hn⟩ := Prod.mk.inj h
    exact OrderedIntermediateField.ext (congr($hf)) hn)

omit [IsOrderedRing K] in
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

omit [IsOrderedRing K] in
@[simp] theorem mem_preordering (P : OrderedIntermediateField K L) (x : P.toIntermediateField) :
    x ∈ P.preordering ↔ x.val ∈ P.nonneg := (Iff.rfl)

instance (P : OrderedIntermediateField K L) : (preordering P).IsOrdering where
  mem_or_neg_mem x := P.mem_or_neg_mem x.val x.property
  toIsPrime := inferInstance

/-- The induced linear order on the intermediate field. -/
@[instance_reducible] noncomputable instance linearOrder (P : OrderedIntermediateField K L) :
    LinearOrder P.toIntermediateField := RingPreordering.linearOrder P.preordering

omit [IsOrderedRing K] in
instance isStrictOrderedRing (P : OrderedIntermediateField K L) :
    IsStrictOrderedRing P.toIntermediateField := RingPreordering.isStrictOrderedRing P.preordering

omit [IsOrderedRing K] in
theorem nonneg_iff (P : OrderedIntermediateField K L) (x : P.toIntermediateField) :
    letI := P.linearOrder
    0 ≤ x ↔ x.val ∈ P.nonneg :=
  (RingPreordering.nonneg_iff P.preordering x).trans (P.mem_preordering x)

theorem algebraMap_strictMono (P : OrderedIntermediateField K L) : letI := P.linearOrder
    StrictMono (algebraMap K P.toIntermediateField) := by
  exact ((monotone_iff_map_nonneg (algebraMap K P.toIntermediateField)).mpr fun x hx =>
    (P.nonneg_iff _).mpr (P.algebraMap_mem_nonneg x hx)).strictMono_of_injective
      (algebraMap K P.toIntermediateField).injective

/-- For `P : OrderedIntermediateField K L`, the order on `P.toIntermediateField` is compatible
with that on `K`. -/
instance (P : OrderedIntermediateField K L) : IsOrderedModule K P.toIntermediateField :=
  IsOrderedModule.of_algebraMap_mono P.algebraMap_strictMono.monotone

/-- For `P : OrderedIntermediateField K L`, converting it to the underlying `IntermediateField K L`
and then converting it back using the inferred instances gives the same result. -/
@[simp] theorem ofIntermediateField_toIntermediateField (P : OrderedIntermediateField K L) :
    ofIntermediateField P.toIntermediateField = P := by
  apply OrderedIntermediateField.ext
  · rfl
  · ext x
    constructor
    · intro hx
      have hxF : x ∈ P.toIntermediateField :=
        (ofIntermediateField P.toIntermediateField).nonneg_subset x hx
      let y : P.toIntermediateField := ⟨x, hxF⟩
      have hy : 0 ≤ y :=
        (mem_nonneg_ofIntermediateField P.toIntermediateField y).mp (by simpa [y] using hx)
      exact (P.nonneg_iff y).mp hy
    · intro hx
      have hxF : x ∈ P.toIntermediateField := P.nonneg_subset x hx
      let y : P.toIntermediateField := ⟨x, hxF⟩
      have hy : 0 ≤ y := (P.nonneg_iff y).mpr (by simpa [y] using hx)
      exact (mem_nonneg_ofIntermediateField P.toIntermediateField y).mpr hy

/-- The base field as an ordered intermediate field. -/
private def base : OrderedIntermediateField K L :=
  image (Algebra.ofId K L)

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

omit [IsOrderedRing K] in
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
    [Field E] [LinearOrder E] [IsOrderedRing E] [Algebra K E]
    [Algebra P.toIntermediateField E] [IsScalarTower K P.toIntermediateField E]
    [IsOrderedModule P.toIntermediateField E]
    (f : E →ₐ[P.toIntermediateField] L) :
    letI := P.linearOrder
    ∃ Q : OrderedIntermediateField K L, P ≤ Q ∧ ∀ x : E, f x ∈ Q.toIntermediateField := by
  have hf : Monotone (algebraMap P.toIntermediateField E) := algebraMap_mono E
  have hbase : Monotone (algebraMap K E) := by
    intro a b hab
    simpa only [← IsScalarTower.algebraMap_apply K P.toIntermediateField E] using
      hf (P.algebraMap_strictMono.monotone hab)
  let hOrderedModule : IsOrderedModule K E := IsOrderedModule.of_algebraMap_mono hbase
  let Q := image (f.restrictScalars K)
  refine ⟨Q, ⟨?_, ?_⟩, fun x => ⟨x, rfl⟩⟩
  · intro x hx
    exact ⟨algebraMap P.toIntermediateField E ⟨x, hx⟩, f.commutes ⟨x, hx⟩⟩
  · intro x hx
    let y : P.toIntermediateField := ⟨x, P.nonneg_subset x hx⟩
    have hy : 0 ≤ y := (P.nonneg_iff y).mpr hx
    exact ⟨algebraMap P.toIntermediateField E y, by simpa using algebraMap_mono E hy, f.commutes y⟩

/-- Every embedding of an ordered extension of a maximal ordered intermediate field `P`
into the ambient field has its image inside `P.toIntermediateField`. -/
theorem mem_of_isMax (P : OrderedIntermediateField K L) (hP : IsMax P) {E : Type*}
    [Field E] [LinearOrder E] [IsOrderedRing E] [Algebra K E]
    [Algebra P.toIntermediateField E] [IsScalarTower K P.toIntermediateField E]
    [IsOrderedModule P.toIntermediateField E]
    (f : E →ₐ[P.toIntermediateField] L) :
    letI := P.linearOrder
    ∀ x : E, f x ∈ P.toIntermediateField := by
  intro x
  obtain ⟨Q, hPQ, hQ⟩ := P.exists_le_mem f
  exact (hP hPQ).1 (hQ x)

end OrderedIntermediateField

end TauCeti.RealClosure
