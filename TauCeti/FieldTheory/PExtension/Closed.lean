/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import TauCeti.FieldTheory.PExtension.Basic
import Mathlib.FieldTheory.PurelyInseparable.Tower

/-!
# `P`-closed and separably `P`-closed fields

For a set `P` of natural numbers, a field `K` is `P`-closed when it has no nontrivial finite
extension whose degree is a `P`-number, and separably `P`-closed when it has no nontrivial finite
separable extension whose degree is a `P`-number (Temkin, *Tame distillation and desingularization
by `p`-alterations*, Annals of Mathematics 186 (2017), §2.1.1). Purely inseparable extensions count
for the first notion, so an imperfect field of characteristic `q ∈ P` is never `P`-closed, while
the separable closure of `𝔽_q(t)` is separably `{q}`-closed. Temkin's tameness theorem for valued
fields is stated for `P`-closed fields, and its form for imperfect fields for separably `P`-closed
fields.

Both predicates are defined by testing the finite subextensions of `AlgebraicClosure K`; the
results below show that any algebraically (resp. separably) closed extension may be used instead,
and that the predicates are equivalently stated for abstract finite extensions.

## Main definitions and results

* `TauCeti.IsPClosed P K`, `TauCeti.IsSeparablyPClosed P K`: `K` has no nontrivial finite
  (separable) extension of `P`-number degree;
* `TauCeti.isPClosed_iff_of_isAlgClosed`, `TauCeti.isSeparablyPClosed_iff_of_isSepClosed`: the
  predicates may be tested in any algebraically (resp. separably) closed extension;
* `TauCeti.isPClosed_iff_forall_isPExtension`,
  `TauCeti.isSeparablyPClosed_iff_forall_isPExtension`: a field is (separably) `P`-closed exactly
  when it has no nontrivial (separable) algebraic `P`-extension;
* `TauCeti.IsPClosed.isSeparablyPClosed`, `TauCeti.isSeparablyPClosed_iff_isPClosed`: `P`-closed
  fields are separably `P`-closed, and the two notions agree for perfect fields;
* `TauCeti.isSeparablyPClosed_iff_of_isPurelyInseparable`: being separably `P`-closed is invariant
  under purely inseparable extensions; consequently
  `TauCeti.isSeparablyPClosed_iff_isPClosed_perfectClosure`: `K` is separably `P`-closed exactly
  when its perfect closure is `P`-closed;
* `TauCeti.isPClosed_of_maximal_isPExtension`,
  `TauCeti.isSeparablyPClosed_of_maximal_isPExtension`: a maximal `P`-subextension of an
  algebraically (resp. separably) closed extension is `P`-closed (resp. separably `P`-closed);
* `TauCeti.IsPClosed.perfectField`: a `P`-closed field whose characteristic exponent is a
  `P`-number is perfect.

The invariance under purely inseparable extensions `L / K` rests on Mathlib's comparison of
separable degrees: a finite separable extension `F / L` has the degree of its separable part over
`K` (`Field.sepDegree_eq_of_isPurelyInseparable_of_isSeparable`), and the compositum `L(S)` of a
finite separable extension `S / K` has the degree of `S`
(`IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable'`).
-/

public section

open Module IntermediateField

namespace TauCeti

universe u

variable (P : Set ℕ) (K : Type u) [Field K]

/-- A field `K` is `P`-closed, for a set `P` of natural numbers, when it has no nontrivial finite
extension whose degree is a `P`-number. Purely inseparable extensions are included. The condition
is tested on the finite subextensions of `AlgebraicClosure K`; see `isPClosed_iff_of_isAlgClosed`
and `isPClosed_iff_forall_isPExtension` for equivalent forms. -/
def IsPClosed : Prop :=
  ∀ E : IntermediateField K (AlgebraicClosure K), FiniteDimensional K E →
    IsPNumber P (finrank K E) → E = ⊥

/-- A field `K` is separably `P`-closed, for a set `P` of natural numbers, when it has no
nontrivial finite separable extension whose degree is a `P`-number. No perfection is imposed. The
condition is tested on the finite separable subextensions of `AlgebraicClosure K`; see
`isSeparablyPClosed_iff_of_isSepClosed` and `isSeparablyPClosed_iff_forall_isPExtension` for
equivalent forms. -/
def IsSeparablyPClosed : Prop :=
  ∀ E : IntermediateField K (AlgebraicClosure K), FiniteDimensional K E →
    Algebra.IsSeparable K E → IsPNumber P (finrank K E) → E = ⊥

variable {P K}

/-- A finite extension `L / K` has degree one when its image under some `K`-embedding into `M` is
`⊥` as soon as that image has `P`-number degree. -/
private theorem finrank_eq_one_of_algHom {L M : Type*} [Field L] [Field M] [Algebra K L]
    [Algebra K M] [FiniteDimensional K L] (f : L →ₐ[K] M)
    (hf : FiniteDimensional K f.fieldRange → IsPNumber P (finrank K f.fieldRange) →
      f.fieldRange = ⊥)
    (hL : IsPNumber P (finrank K L)) : finrank K L = 1 := by
  let e := f.equivFieldRange
  have hfin : FiniteDimensional K f.fieldRange := e.toLinearEquiv.finiteDimensional
  rw [e.toLinearEquiv.finrank_eq, IntermediateField.finrank_eq_one_iff]
  exact hf hfin (e.toLinearEquiv.finrank_eq ▸ hL)

/-- A `P`-subextension `E` of `M / K` is `⊥` as soon as `K⟮x⟯ = ⊥` for every `x ∈ E` for which
`K⟮x⟯` is finite of `P`-number degree. -/
private theorem eq_bot_of_isPExtension_of_adjoin_simple {M : Type*} [Field M] [Algebra K M]
    {E : IntermediateField K M} (hE : IsPExtension P K E)
    (h : ∀ x ∈ E, FiniteDimensional K K⟮x⟯ → IsPNumber P (finrank K K⟮x⟯) →
      K⟮x⟯ = ⊥) :
    E = ⊥ := by
  refine eq_bot_iff.2 fun x hx ↦ ?_
  have hfin : FiniteDimensional K K⟮x⟯ := adjoin.finiteDimensional <|
    isIntegral_iff.1 (hE.isAlgebraic.isAlgebraic (⟨x, hx⟩ : E)).isIntegral
  have hle : K⟮x⟯ ≤ E := adjoin_simple_le_iff.2 hx
  rw [← h x hx hfin ((isPExtension_intermediateField_iff.1 hE).2 _ hle hfin)]
  exact mem_adjoin_simple_self K x

section IsPClosed

/-- A `P`-closed field has no nontrivial finite extension of `P`-number degree. -/
theorem IsPClosed.finrank_eq_one (h : IsPClosed P K) (L : Type*) [Field L] [Algebra K L]
    [FiniteDimensional K L] (hL : IsPNumber P (finrank K L)) : finrank K L = 1 :=
  finrank_eq_one_of_algHom (IsAlgClosed.lift : L →ₐ[K] AlgebraicClosure K) (h _) hL

/-- Over a `P`-closed field, every finite subextension of `P`-number degree is trivial. -/
theorem IsPClosed.eq_bot (h : IsPClosed P K) {M : Type*} [Field M] [Algebra K M]
    (E : IntermediateField K M) [FiniteDimensional K E] (hE : IsPNumber P (finrank K E)) :
    E = ⊥ :=
  IntermediateField.finrank_eq_one_iff.1 (h.finrank_eq_one E hE)

/-- Being `P`-closed may be tested in any algebraically closed extension `M` of `K`. -/
theorem isPClosed_iff_of_isAlgClosed (M : Type*) [Field M] [Algebra K M] [IsAlgClosed M] :
    IsPClosed P K ↔ ∀ E : IntermediateField K M, FiniteDimensional K E →
      IsPNumber P (finrank K E) → E = ⊥ :=
  ⟨fun h E _ hE ↦ h.eq_bot E hE, fun h E _ hE ↦
    IntermediateField.finrank_eq_one_iff.1 <|
      finrank_eq_one_of_algHom (IsAlgClosed.lift : E →ₐ[K] M) (h _) hE⟩

/-- Over a `P`-closed field, every algebraic `P`-subextension is trivial. -/
theorem IsPClosed.eq_bot_of_isPExtension (h : IsPClosed P K) {M : Type*} [Field M] [Algebra K M]
    {E : IntermediateField K M} (hE : IsPExtension P K E) : E = ⊥ :=
  eq_bot_of_isPExtension_of_adjoin_simple hE fun x _ _ hx ↦ h.eq_bot K⟮x⟯ hx

/-- A `P`-closed field has no nontrivial algebraic `P`-extension. -/
theorem IsPClosed.finrank_eq_one_of_isPExtension (h : IsPClosed P K) {L : Type*} [Field L]
    [Algebra K L] (hL : IsPExtension P K L) : finrank K L = 1 :=
  bot_eq_top_iff_finrank_eq_one.1 <|
    (h.eq_bot_of_isPExtension ((isPExtension_congr topEquiv).2 hL)).symm

/-- A field is `P`-closed exactly when it has no nontrivial algebraic `P`-extension. -/
theorem isPClosed_iff_forall_isPExtension :
    IsPClosed P K ↔
      ∀ (L : Type u) [Field L] [Algebra K L], IsPExtension P K L → finrank K L = 1 :=
  ⟨fun h _ _ _ hL ↦ h.finrank_eq_one_of_isPExtension hL, fun h E _ hE ↦
    IntermediateField.finrank_eq_one_iff.1 (h E (isPExtension_iff_isPNumber_finrank.2 hE))⟩

/-- Shrinking `P` preserves `P`-closed fields. -/
theorem IsPClosed.mono {Q : Set ℕ} (h : IsPClosed Q K) (hPQ : P ⊆ Q) : IsPClosed P K :=
  fun E hE hP ↦ h E hE (hP.mono hPQ)

variable (K) in
/-- Every field is `∅`-closed: the only `∅`-number is `1`. -/
@[simp]
theorem isPClosed_empty : IsPClosed ∅ K :=
  fun _ _ hE ↦ IntermediateField.finrank_eq_one_iff.1 (isPNumber_empty_iff.1 hE)

end IsPClosed

section IsSeparablyPClosed

/-- A separably `P`-closed field has no nontrivial finite separable extension of `P`-number
degree. -/
theorem IsSeparablyPClosed.finrank_eq_one (h : IsSeparablyPClosed P K) (L : Type*) [Field L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hL : IsPNumber P (finrank K L)) : finrank K L = 1 := by
  let f : L →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  exact finrank_eq_one_of_algHom f
    (fun hfin ↦ h _ hfin (AlgEquiv.Algebra.isSeparable (f.equivFieldRange))) hL

/-- Over a separably `P`-closed field, every finite separable subextension of `P`-number degree is
trivial. -/
theorem IsSeparablyPClosed.eq_bot (h : IsSeparablyPClosed P K) {M : Type*} [Field M]
    [Algebra K M] (E : IntermediateField K M) [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (hE : IsPNumber P (finrank K E)) : E = ⊥ :=
  IntermediateField.finrank_eq_one_iff.1 (h.finrank_eq_one E hE)

/-- Being separably `P`-closed may be tested in any separably closed extension `M` of `K`. -/
theorem isSeparablyPClosed_iff_of_isSepClosed (M : Type*) [Field M] [Algebra K M]
    [IsSepClosed M] :
    IsSeparablyPClosed P K ↔ ∀ E : IntermediateField K M, FiniteDimensional K E →
      Algebra.IsSeparable K E → IsPNumber P (finrank K E) → E = ⊥ := by
  refine ⟨fun h E _ _ hE ↦ h.eq_bot E hE, fun h E _ _ hE ↦ ?_⟩
  let f : E →ₐ[K] M := IsSepClosed.lift
  exact IntermediateField.finrank_eq_one_iff.1 <| finrank_eq_one_of_algHom f
    (fun hfin ↦ h _ hfin (AlgEquiv.Algebra.isSeparable (f.equivFieldRange))) hE

/-- Over a separably `P`-closed field, every separable algebraic `P`-subextension is trivial. -/
theorem IsSeparablyPClosed.eq_bot_of_isPExtension (h : IsSeparablyPClosed P K) {M : Type*}
    [Field M] [Algebra K M] {E : IntermediateField K M} [Algebra.IsSeparable K E]
    (hE : IsPExtension P K E) : E = ⊥ :=
  eq_bot_of_isPExtension_of_adjoin_simple hE fun x hx _ hdeg ↦
    have : Algebra.IsSeparable K K⟮x⟯ := .of_algHom K E (inclusion (adjoin_simple_le_iff.2 hx))
    h.eq_bot K⟮x⟯ hdeg

/-- A separably `P`-closed field has no nontrivial separable algebraic `P`-extension. -/
theorem IsSeparablyPClosed.finrank_eq_one_of_isPExtension (h : IsSeparablyPClosed P K)
    {L : Type*} [Field L] [Algebra K L] [Algebra.IsSeparable K L] (hL : IsPExtension P K L) :
    finrank K L = 1 := by
  have : Algebra.IsSeparable K (⊤ : IntermediateField K L) :=
    AlgEquiv.Algebra.isSeparable topEquiv.symm
  exact bot_eq_top_iff_finrank_eq_one.1 <|
    (h.eq_bot_of_isPExtension ((isPExtension_congr topEquiv).2 hL)).symm

/-- A field is separably `P`-closed exactly when it has no nontrivial separable algebraic
`P`-extension. -/
theorem isSeparablyPClosed_iff_forall_isPExtension :
    IsSeparablyPClosed P K ↔ ∀ (L : Type u) [Field L] [Algebra K L] [Algebra.IsSeparable K L],
      IsPExtension P K L → finrank K L = 1 :=
  ⟨fun h _ _ _ _ hL ↦ h.finrank_eq_one_of_isPExtension hL, fun h E _ _ hE ↦
    IntermediateField.finrank_eq_one_iff.1 (h E (isPExtension_iff_isPNumber_finrank.2 hE))⟩

/-- Shrinking `P` preserves separably `P`-closed fields. -/
theorem IsSeparablyPClosed.mono {Q : Set ℕ} (h : IsSeparablyPClosed Q K) (hPQ : P ⊆ Q) :
    IsSeparablyPClosed P K :=
  fun E hE hsep hP ↦ h E hE hsep (hP.mono hPQ)

/-- A `P`-closed field is separably `P`-closed. -/
theorem IsPClosed.isSeparablyPClosed (h : IsPClosed P K) : IsSeparablyPClosed P K :=
  fun E hfin _ hE ↦ h E hfin hE

/-- For a perfect field, for instance one of characteristic zero, being separably `P`-closed is
the same as being `P`-closed. -/
theorem isSeparablyPClosed_iff_isPClosed [PerfectField K] :
    IsSeparablyPClosed P K ↔ IsPClosed P K :=
  ⟨fun h E _ hE ↦ h E ‹_› inferInstance hE, IsPClosed.isSeparablyPClosed⟩

variable (P K) in
/-- A separably closed field is separably `P`-closed for every `P`. -/
theorem isSeparablyPClosed_of_isSepClosed [IsSepClosed K] : IsSeparablyPClosed P K :=
  fun E _ _ _ ↦ eq_bot_of_isSepClosed_of_isSeparable E

variable (P K) in
/-- An algebraically closed field is `P`-closed for every `P`. -/
theorem isPClosed_of_isAlgClosed [IsAlgClosed K] : IsPClosed P K :=
  isSeparablyPClosed_iff_isPClosed.1 (isSeparablyPClosed_of_isSepClosed P K)

end IsSeparablyPClosed

section PurelyInseparable

variable (L : Type*) [Field L] [Algebra K L] [IsPurelyInseparable K L]

/-- Over a purely inseparable extension `L` of a separably `P`-closed field `K`, a finite separable
extension `F / L` of `P`-number degree is trivial: its separable part over `K` has degree `[F : L]`
over `K`. -/
private theorem IsSeparablyPClosed.finrank_eq_one_of_isPurelyInseparable
    (h : IsSeparablyPClosed P K) (F : Type*) [Field F] [Algebra L F] [FiniteDimensional L F]
    [Algebra.IsSeparable L F] (hF : IsPNumber P (finrank L F)) : finrank L F = 1 := by
  let : Algebra K F := ((algebraMap L F).comp (algebraMap K L)).toAlgebra
  have : IsScalarTower K L F := .of_algebraMap_eq fun _ ↦ rfl
  have hrank : Module.rank K (separableClosure K F) = Module.rank L F :=
    Field.sepDegree_eq_of_isPurelyInseparable_of_isSeparable K L F
  have : FiniteDimensional K (separableClosure K F) :=
    Module.rank_lt_aleph0_iff.1 (hrank ▸ Module.rank_lt_aleph0 L F)
  have hfinrank : finrank K (separableClosure K F) = finrank L F :=
    finrank_eq_of_rank_eq (hrank.trans (finrank_eq_rank L F).symm)
  rw [← hfinrank, IntermediateField.finrank_eq_one_iff]
  exact h.eq_bot _ (hfinrank ▸ hF)

/-- Below a purely inseparable extension `L` of `K`, a separably `P`-closed `L` makes `K` separably
`P`-closed: a finite separable extension `S / K` has the same degree as its compositum `L(S)` with
`L` inside an algebraic closure of `L`. -/
private theorem IsSeparablyPClosed.of_isPurelyInseparable (h : IsSeparablyPClosed P L) :
    IsSeparablyPClosed P K := by
  intro E _ _ hE
  let f : E →ₐ[K] AlgebraicClosure L := IsAlgClosed.lift
  let e := f.equivFieldRange
  let S := f.fieldRange
  have : Algebra.IsSeparable K S := AlgEquiv.Algebra.isSeparable e
  have : FiniteDimensional K S := e.toLinearEquiv.finiteDimensional
  have hS : S ≤ separableClosure K (AlgebraicClosure L) :=
    (le_separableClosure_iff _ _ _).2 ‹_›
  let F := adjoin L (S : Set (AlgebraicClosure L))
  have : Algebra.IsSeparable L F := (isSeparable_adjoin_iff_isSeparable L _).2 fun x hx ↦
    (mem_separableClosure_iff.1 (hS hx)).tower_top L
  have hrank : Module.rank L F = Module.rank K S := by
    rw [← Algebra.IsSeparable.sepDegree_eq, ← Algebra.IsSeparable.sepDegree_eq]
    exact sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable' L S
  have : FiniteDimensional L F := Module.rank_lt_aleph0_iff.1 (hrank ▸ Module.rank_lt_aleph0 K S)
  have hfinrank : finrank L F = finrank K E :=
    (finrank_eq_of_rank_eq (hrank.trans (finrank_eq_rank K S).symm)).trans
      e.toLinearEquiv.finrank_eq.symm
  rw [← IntermediateField.finrank_eq_one_iff, ← hfinrank, IntermediateField.finrank_eq_one_iff]
  exact h.eq_bot F (hfinrank ▸ hE)

/-- Being separably `P`-closed is invariant under purely inseparable extensions. -/
theorem isSeparablyPClosed_iff_of_isPurelyInseparable :
    IsSeparablyPClosed P K ↔ IsSeparablyPClosed P L :=
  ⟨fun h E _ _ hE ↦
    IntermediateField.finrank_eq_one_iff.1 (h.finrank_eq_one_of_isPurelyInseparable L E hE),
    IsSeparablyPClosed.of_isPurelyInseparable L⟩

/-- If `L / K` is purely inseparable and `L` is perfect, then `K` is separably `P`-closed exactly
when `L` is `P`-closed. -/
theorem isSeparablyPClosed_iff_isPClosed_of_isPurelyInseparable [PerfectField L] :
    IsSeparablyPClosed P K ↔ IsPClosed P L :=
  (isSeparablyPClosed_iff_of_isPurelyInseparable L).trans isSeparablyPClosed_iff_isPClosed

variable (P K) in
/-- A field is separably `P`-closed exactly when its perfect closure is `P`-closed. -/
theorem isSeparablyPClosed_iff_isPClosed_perfectClosure :
    IsSeparablyPClosed P K ↔ IsPClosed P (perfectClosure K (AlgebraicClosure K)) :=
  isSeparablyPClosed_iff_isPClosed_of_isPurelyInseparable _

end PurelyInseparable

section Maximal

variable {M : Type*} [Field M] [Algebra K M] {E : IntermediateField K M}

/-- A maximal `P`-subextension of an algebraically closed extension of `K` is `P`-closed. -/
theorem isPClosed_of_maximal_isPExtension [IsAlgClosed M]
    (hE : Maximal (fun E : IntermediateField K M ↦ IsPExtension P K E) E) : IsPClosed P E :=
  (isPClosed_iff_of_isAlgClosed M).2 fun _ _ hN ↦
    eq_bot_of_maximal_isPExtension hE (isPExtension_iff_isPNumber_finrank.2 hN)

/-- A maximal `P`-subextension of a separably closed extension of `K` is separably `P`-closed. -/
theorem isSeparablyPClosed_of_maximal_isPExtension [IsSepClosed M]
    (hE : Maximal (fun E : IntermediateField K M ↦ IsPExtension P K E) E) :
    IsSeparablyPClosed P E :=
  (isSeparablyPClosed_iff_of_isSepClosed M).2 fun _ _ _ hN ↦
    eq_bot_of_maximal_isPExtension hE (isPExtension_iff_isPNumber_finrank.2 hN)

end Maximal

/-- A `P`-closed field whose characteristic exponent `q` is a `P`-number is perfect: its finite
purely inseparable extensions have degree a power of `q`. For `q` prime the hypothesis says
`q ∈ P`, and in characteristic zero it always holds. -/
theorem IsPClosed.perfectField (h : IsPClosed P K) (q : ℕ) [ExpChar K q] (hq : IsPNumber P q) :
    PerfectField K := by
  refine perfectField_of_perfectClosure_eq_bot K (AlgebraicClosure K)
    (h.eq_bot_of_isPExtension ⟨inferInstance, fun F _ ↦ ?_⟩)
  have : IsPurelyInseparable K F :=
    IsPurelyInseparable.tower_bot K F (perfectClosure K (AlgebraicClosure K))
  obtain ⟨n, hn⟩ := IsPurelyInseparable.finrank_eq_pow K F q
  exact hn ▸ hq.pow n

end TauCeti
