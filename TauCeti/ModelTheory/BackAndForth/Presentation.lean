/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.PotentialIso
public import TauCeti.ModelTheory.BackAndForth.TupleSystem

/-!
# The two presentations of back-and-forth systems

For relational languages, tuple back-and-forth systems and systems of finitely generated
partial equivalences give the same notion of potential isomorphism. Matching atomic types
produce an equivalence between the finite ranges of the tuples. Conversely, a partial
equivalence preserves the atomic type of every tuple in its domain. Neither countability nor
nonemptiness of the structures is required; nullary relations are retained. When the first
tuple is onto its structure, matching atomic types even give an embedding of the whole structure.

The comparison is the relational back-and-forth argument of Carol Karp,
*Finite-quantifier equivalence* (1965). The tuple presentation also appears in Cameron Freer's
`cameronfreer/infinitary-logic`, `InfinitaryLogic/Karp/PotentialIso.lean` at checkpoint
`9f82bd572af2d79a043c6bc3f1b745f14e0bcaa4`. Here potential isomorphism uses Mathlib's
`FGEquiv`, and the comparison with tuple systems is explicit.
-/

public section

universe u v w w'

namespace TauCeti

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure Fin

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-- A partial equivalence preserves the atomic type of each tuple in its domain. -/
theorem _root_.FirstOrder.Language.PartialEquiv.sameAtomicType (f : M ≃ₚ[L] N)
    {n : ℕ} (a : Fin n → f.dom) :
    SameAtomicType (L := L) (fun i => (a i : M)) (f.toEmbedding ∘ a) := by
  rw [sameAtomicType_iff]
  refine ⟨fun i j => ?_, fun r g => ?_⟩
  · exact ⟨fun hij => congrArg f.toEmbedding (Subtype.ext hij),
      fun hij => congrArg Subtype.val (f.toEmbedding.injective hij)⟩
  · exact (f.dom.subtype.map_rel r (a ∘ g)).trans
      (f.toEmbedding.map_rel r (a ∘ g)).symm

omit [L.IsRelational] in
/-- If the domain of a partial equivalence `f` is enumerated by a tuple `a` that `f` sends to `b`,
then every partial equivalence sending `a` to `b` extends `f`. -/
theorem _root_.FirstOrder.Language.PartialEquiv.le_of_dom_eq_range {f g : M ≃ₚ[L] N} {n : ℕ}
    {a : Fin n → M} {b : Fin n → N} (a' : Fin n → f.dom) (ha : ∀ i, (a' i : M) = a i)
    (hb : ∀ i, f.toEmbedding (a' i) = b i) (hd : (f.dom : Set M) = Set.range a)
    (c : Fin n → g.dom) (hc : ∀ i, (c i : M) = a i) (he : ∀ i, g.toEmbedding (c i) = b i) :
    f ≤ g := by
  have hle : f.dom ≤ g.dom := by
    intro z hz
    have hz' : z ∈ Set.range a := by rw [← hd]; exact hz
    obtain ⟨i, rfl⟩ := hz'
    exact hc i ▸ (c i).property
  apply (PartialEquiv.le_def _ _).mpr
  refine ⟨hle, ?_⟩
  -- Equality of the embeddings is checked on the tuple enumerating the whole domain.
  ext z
  have hz' : (z : M) ∈ Set.range a := by rw [← hd]; exact z.property
  obtain ⟨i, hi⟩ := hz'
  have hz : a' i = z := Subtype.ext ((ha i).trans hi)
  subst z
  have hc' : c i = Substructure.inclusion hle (a' i) :=
    Subtype.ext (by simp only [Substructure.coe_inclusion, ha, hc])
  exact (congrArg g.toEmbedding hc').symm.trans ((he i).trans (hb i).symm)

/-- Tuples with matching atomic types induce a finitely generated partial equivalence whose
whole domain is the range of the first tuple. Repeated entries are allowed. -/
theorem SameAtomicType.exists_fgEquiv {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : SameAtomicType (L := L) a b) :
    ∃ (f : L.FGEquiv M N) (a' : Fin n → f.1.dom),
      (∀ i, (a' i : M) = a i) ∧ (∀ i, f.1.toEmbedding (a' i) = b i) ∧
        (f.1.dom : Set M) = Set.range a := by
  classical
  let A := Substructure.closure L (Set.range a)
  let idx (x : A) := Set.rangeSplitting a
    ⟨x, (Substructure.mem_closure_iff_of_isRelational L _ _).mp x.property⟩
  have hidx (x : A) : a (idx x) = (x : M) := Set.apply_rangeSplitting a _
  have hmap (i : Fin n) (x : A) (hx : (x : M) = a i) : b (idx x) = b i :=
    (h.eq_iff _ _).mp ((hidx x).trans hx)
  let e : A ↪[L] N :=
    { toFun := fun x => b (idx x)
      inj' := by
        intro x y hxy
        exact Subtype.ext ((hidx x).symm.trans (((h.eq_iff _ _).mpr hxy).trans (hidx y)))
      map_fun' := fun f => isEmptyElim f
      map_rel' := by
        intro k r x
        have hr := (h.rel_iff r (idx ∘ x)).symm
        simp only [Function.comp_def, hidx] at hr
        exact hr.trans (A.subtype.map_rel r x) }
  let f : L.FGEquiv M N :=
    ⟨⟨A, e.toHom.range, e.equivRange⟩,
      Substructure.fg_iff_exists_fin_generating_family.mpr ⟨n, a, rfl⟩⟩
  let a' : Fin n → A := fun i => ⟨a i, Substructure.subset_closure (Set.mem_range_self i)⟩
  refine ⟨f, a', fun _ => rfl, ?_, Substructure.closure_eq_of_isRelational L _⟩
  intro i
  exact (e.equivRange_apply (a' i)).trans (hmap i (a' i) rfl)

/-- If a tuple onto `M` has the same atomic type as a tuple `b` of `N`, then sending each entry
to the corresponding entry of `b` is an embedding of `M` into `N`. Repeated entries are
allowed. -/
theorem SameAtomicType.exists_embedding_comp_eq {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : SameAtomicType (L := L) a b) (ha : Function.Surjective a) :
    ∃ f : M ↪[L] N, f ∘ a = b := by
  obtain ⟨f, a', ha', hb', hdom⟩ := h.exists_fgEquiv
  have hdom' : f.1.dom = ⊤ := SetLike.coe_injective (hdom.trans (Set.range_eq_univ.mpr ha))
  refine ⟨PartialEquiv.toEmbeddingOfEqTop hdom', funext fun i => ?_⟩
  rw [Function.comp_apply, PartialEquiv.toEmbeddingOfEqTop_apply, ← hb' i]
  exact congrArg f.1.toEmbedding (Subtype.ext (ha' i).symm)

/-- A tuple back-and-forth system gives a system of finitely generated partial equivalences,
closed under extensions on both sides, in which each pair of the tuple system is matched by some
member. -/
theorem IsTupleBFSystem.exists_fgEquiv_system
    {S : Set (Σ n, (Fin n → M) × (Fin n → N))} (hS : IsTupleBFSystem (L := L) S) {n : ℕ}
    {a : Fin n → M} {b : Fin n → N} (hab : ⟨n, a, b⟩ ∈ S) :
    ∃ T : Set (L.FGEquiv M N), (∀ f ∈ T, ∀ m : M, ∃ g ∈ T, m ∈ g.1.dom ∧ f ≤ g) ∧
      (∀ f ∈ T, ∀ y : N, ∃ g ∈ T, y ∈ g.1.cod ∧ f ≤ g) ∧
      ∃ f ∈ T, ∃ a' : Fin n → f.1.dom,
        (∀ i, (a' i : M) = a i) ∧ ∀ i, f.1.toEmbedding (a' i) = b i := by
  -- Use only partial equivalences whose whole domains are enumerated by pairs in the system.
  let T : Set (L.FGEquiv M N) := {f | ∃ (n : ℕ) (a : Fin n → M) (b : Fin n → N),
    ⟨n, a, b⟩ ∈ S ∧ ∃ a' : Fin n → f.1.dom,
      (∀ i, (a' i : M) = a i) ∧ (∀ i, f.1.toEmbedding (a' i) = b i) ∧
        (f.1.dom : Set M) = Set.range a}
  have extend {f : L.FGEquiv M N} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
      (a' : Fin n → f.1.dom) (ha : ∀ i, (a' i : M) = a i)
      (hb : ∀ i, f.1.toEmbedding (a' i) = b i) (hd : (f.1.dom : Set M) = Set.range a)
      {x : M} {y : N} (hxy : ⟨n + 1, snoc a x, snoc b y⟩ ∈ S) :
      ∃ g ∈ T, x ∈ g.1.dom ∧ y ∈ g.1.cod ∧ f ≤ g := by
    obtain ⟨g, c, hc, he, hgdom⟩ := (hS.sameAtomicType hxy).exists_fgEquiv
    refine ⟨g, ⟨n + 1, snoc a x, snoc b y, hxy, c, hc, he, hgdom⟩, ?_, ?_, ?_⟩
    · exact (by simpa only [snoc_last] using hc (last n)) ▸ (c (last n)).property
    · have hy := (g.1.toEquiv (c (last n))).property
      exact (by simpa only [snoc_last] using he (last n)) ▸ hy
    · exact PartialEquiv.le_of_dom_eq_range a' ha hb hd (fun i => c i.castSucc)
        (fun i => by simpa only [snoc_castSucc] using hc i.castSucc)
        (fun i => by simpa only [snoc_castSucc] using he i.castSucc)
  refine ⟨T, ?_, ?_, ?_⟩
  · rintro f ⟨n, a, b, hab, a', ha, hb, hd⟩ x
    obtain ⟨y, hxy⟩ := hS.forth hab x
    obtain ⟨g, hg, hx, _, hfg⟩ := extend a' ha hb hd hxy
    exact ⟨g, hg, hx, hfg⟩
  · rintro f ⟨n, a, b, hab, a', ha, hb, hd⟩ y
    obtain ⟨x, hxy⟩ := hS.back hab y
    obtain ⟨g, hg, _, hy, hfg⟩ := extend a' ha hb hd hxy
    exact ⟨g, hg, hy, hfg⟩
  · obtain ⟨f, a', ha, hb, hd⟩ := (hS.sameAtomicType hab).exists_fgEquiv
    exact ⟨f, ⟨n, a, b, hab, a', ha, hb, hd⟩, a', ha, hb⟩

/-- A tuple back-and-forth system gives a system of finitely generated partial equivalences. -/
theorem IsTupleBFSystem.potentialIso
    {S : Set (Σ n, (Fin n → M) × (Fin n → N))} (hS : IsTupleBFSystem (L := L) S) :
    PotentialIso (L := L) M N :=
  let ⟨T, hforth, hback, f, hf, _⟩ := hS.exists_fgEquiv_system hS.empty_mem
  potentialIso_def.mpr ⟨T, ⟨f, hf⟩, hforth, hback⟩

/-- A system of finitely generated partial equivalences supplies a tuple back-and-forth system
by taking all tuples whose entries are simultaneously matched by a member of the system. -/
theorem PotentialIso.exists_isTupleBFSystem (h : PotentialIso (L := L) M N) :
    ∃ S : Set (Σ n, (Fin n → M) × (Fin n → N)), IsTupleBFSystem (L := L) S := by
  obtain ⟨T, ⟨f₀, hf₀⟩, hforth, hback⟩ := potentialIso_def.mp h
  let S : Set (Σ n, (Fin n → M) × (Fin n → N)) :=
    {p | ∃ f ∈ T, ∃ a : Fin p.1 → f.1.dom,
      (∀ i, (a i : M) = p.2.1 i) ∧ (∀ i, f.1.toEmbedding (a i) = p.2.2 i)}
  have extend {f g : L.FGEquiv M N} (hfg : f ≤ g) {n : ℕ}
      (a : Fin n → f.1.dom) {b : Fin n → N} (hb : ∀ i, f.1.toEmbedding (a i) = b i) :
      ∀ i, g.1.toEmbedding (Substructure.inclusion (PartialEquiv.dom_le_dom hfg) (a i)) =
        b i := by
    intro i
    exact (congrArg Subtype.val (PartialEquiv.toEquiv_inclusion_apply hfg (a i))).trans (hb i)
  refine ⟨S, ⟨?_, ?_, ?_, ?_⟩⟩
  · exact ⟨f₀, hf₀, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  · rintro n a b ⟨f, _, a', ha, hb⟩
    convert f.1.sameAtomicType a' using 1 <;> funext i
    · exact (ha i).symm
    · exact (hb i).symm
  · rintro n a b ⟨f, hf, a', ha, hb⟩ x
    obtain ⟨g, hg, hx, hfg⟩ := hforth f hf x
    let c := Substructure.inclusion (PartialEquiv.dom_le_dom hfg) ∘ a'
    refine ⟨g.1.toEmbedding ⟨x, hx⟩, g, hg, snoc c ⟨x, hx⟩, ?_, ?_⟩
    · intro i
      exact lastCases (by simp) (fun j => by simpa [c] using ha j) i
    · intro i
      exact lastCases (by simp) (fun j => by simpa [c] using extend hfg a' hb j) i
  · rintro n a b ⟨f, hf, a', ha, hb⟩ y
    obtain ⟨g, hg, hy, hfg⟩ := hback f hf y
    let c := Substructure.inclusion (PartialEquiv.dom_le_dom hfg) ∘ a'
    let x := g.1.toEquiv.symm ⟨y, hy⟩
    refine ⟨(x : M), g, hg, snoc c x, ?_, ?_⟩
    · intro i
      exact lastCases (by simp) (fun j => by simpa [c] using ha j) i
    · intro i
      exact lastCases (by simp [x]) (fun j => by simpa [c] using extend hfg a' hb j) i

/-- For relational languages, potential isomorphism is equivalently witnessed by a tuple
back-and-forth system. This includes empty structures and languages with nullary relations. -/
theorem potentialIso_iff_exists_isTupleBFSystem :
    PotentialIso (L := L) M N ↔
      ∃ S : Set (Σ n, (Fin n → M) × (Fin n → N)), IsTupleBFSystem (L := L) S :=
  ⟨PotentialIso.exists_isTupleBFSystem, fun ⟨_, hS⟩ => hS.potentialIso⟩

end TauCeti
