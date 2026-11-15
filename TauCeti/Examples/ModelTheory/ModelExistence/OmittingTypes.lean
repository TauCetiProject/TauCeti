/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.ModelExistence.OmittingTypes
public import TauCeti.ModelTheory.Basic
import TauCeti.ModelTheory.Infinitary.ConstantSupport
import TauCeti.ModelTheory.LanguageMap
import TauCeti.ModelTheory.Semantics
import TauCeti.ModelTheory.Term.Constants

/-!
# First-order omitting types compared with `Theory.IsSatisfiable`

Over the countable language `Language.empty[[ℕ]]` consisting solely of countably many constant
symbols `c_k` (`k : ℕ`), Mathlib's `Language.empty.distinctConstantsTheory Set.univ` asserts all
pairwise inequalities `c_i ≠ c_j` (`i ≠ j`). Its standard model `StdNat` interprets `c_k` as `⟨k⟩`.

The partial 1-type `unnamedType` consisting of the formulas `x ≠ c_k` for all `k : ℕ` separates the
first-order omitting types theorem (`FirstOrder.Language.Theory.exists_countable_model_omitting`)
from first-order satisfiability (`FirstOrder.Language.Theory.IsSatisfiable`):

* **Compactness via `Theory.IsSatisfiable`**: for *every* first-order theory `T` satisfied by
  `StdNat`, including both `distinctTheory` and the complete theory `completeTheory StdNat`, every
  finite subset of `unnamedType` is realized in `StdNat`, so by
  `Theory.exists_modelType_realize_iff_forall_finset_isSatisfiable`, `T` has a nonempty model
  realizing `unnamedType` (containing an unnamed element, hence not isomorphic to `StdNat`). Every
  finite subset of `unnamedType` is likewise isolated modulo `distinctTheory`
  (`Theory.exists_isolating_iff_of_finite`).
* **Omitting `unnamedType`**: no single first-order formula isolates `unnamedType` modulo
  `distinctTheory`, because any candidate formula mentions only finitely many constants, allowing a
  fresh constant to be reinterpreted at a witness without breaking pairwise distinctness. Thus
  `Theory.exists_countable_model_omitting` produces, in every universe `w`, a countable model of
  `distinctTheory` omitting `unnamedType`. A structure models `distinctTheory` and omits
  `unnamedType` if and only if it is isomorphic to `StdNat`.
* **Contrast with isolated types**: the partial 1-type `namedType k` asserting `x = c_k` is realized
  in every nonempty model of `distinctTheory`, and is therefore isolated modulo `distinctTheory` by
  `Theory.exists_isolating_of_realized_in_every_countable_model`.

## Main definitions

* `TauCeti.DistinctConstantsOmitting.ConstLang`: the countable constant language
  `Language.empty[[ℕ]]`.
* `TauCeti.DistinctConstantsOmitting.StdNat`: the standard structure interpreting the `k`-th
  constant as `⟨k⟩`.
* `TauCeti.DistinctConstantsOmitting.distinctTheory`: the theory of pairwise distinct constants.
* `TauCeti.DistinctConstantsOmitting.unnamedType`: the partial 1-type `{x₀ ≠ c_k | k : ℕ}`.
* `TauCeti.DistinctConstantsOmitting.namedType`: the singleton partial 1-type `{x₀ = c_k}`.

## Main results

* `TauCeti.DistinctConstantsOmitting.nonempty_equiv_stdNat_iff`: a structure is isomorphic to
  `StdNat` if and only if it models `distinctTheory` and omits `unnamedType`.
* `TauCeti.DistinctConstantsOmitting.exists_modelType_realize_unnamedType_of_stdNat_model` and
  `TauCeti.DistinctConstantsOmitting.exists_modelType_completeTheory_stdNat_not_equiv`: every
  first-order theory satisfied by `StdNat` (even its complete theory) has a model realizing
  `unnamedType`, hence not isomorphic to `StdNat`.
* `TauCeti.DistinctConstantsOmitting.not_exists_isolating_unnamedType`: `unnamedType` is not
  isolated by any first-order formula modulo `distinctTheory`.
* `TauCeti.DistinctConstantsOmitting.exists_countable_model_omitting_unnamedType`: in every
  universe `w`, `distinctTheory` has a countable nonempty model omitting `unnamedType`, isomorphic
  to `StdNat`.
* `TauCeti.DistinctConstantsOmitting.exists_isolating_namedType`: `namedType k` is isolated modulo
  `distinctTheory`.

## References

* D. Marker, *Model Theory: An Introduction*, Springer, 2002, Example 4.2.3.
* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, Chapter 4.
-/

public section

universe w

open FirstOrder FirstOrder.Language

namespace TauCeti.DistinctConstantsOmitting

/-- The countable language with countably many constant symbols indexed by `ℕ` and no other
function or relation symbols. -/
abbrev ConstLang : Language.{0, 0} := Language.empty[[ℕ]]

/-- The standard carrier wrapping `ℕ` for `ConstLang`, defined as a structure so its
`ConstLang`-structure does not pollute global instance search on `ℕ`. -/
structure StdNat where
  /-- The underlying natural number. -/
  val : ℕ
  deriving DecidableEq

/-- The canonical bijection between `StdNat` and `ℕ`. -/
def StdNat.equivNat : StdNat ≃ ℕ where
  toFun := StdNat.val
  invFun := StdNat.mk
  left_inv := fun ⟨_⟩ => rfl
  right_inv := fun _ => rfl

@[simp]
theorem StdNat.equivNat_apply (x : StdNat) : x.equivNat = x.val := (rfl)

@[simp]
theorem StdNat.equivNat_symm_apply (k : ℕ) : StdNat.equivNat.symm k = ⟨k⟩ := (rfl)

instance : Nonempty StdNat := ⟨⟨0⟩⟩

instance : Countable StdNat := StdNat.equivNat.injective.countable

instance : Infinite StdNat :=
  Infinite.of_injective StdNat.equivNat.symm StdNat.equivNat.symm.injective

instance : Language.empty.Structure StdNat := Language.emptyStructure

instance : (constantsOn ℕ).Structure StdNat := constantsOn.structure StdNat.mk

/-- In `StdNat`, the `k`-th constant symbol evaluates to `⟨k⟩`. -/
@[simp]
theorem coe_con_stdNat (k : ℕ) :
    (Language.empty.con k : StdNat) = ⟨k⟩ := (rfl)

/-- The first-order theory asserting that all constants `c_k` (`k : ℕ`) are pairwise distinct,
defined as Mathlib's `Language.distinctConstantsTheory` on `Set.univ`. -/
def distinctTheory : ConstLang.Theory :=
  Language.empty.distinctConstantsTheory Set.univ

/-- `distinctTheory` is `Language.empty.distinctConstantsTheory Set.univ`. -/
theorem distinctTheory_def :
    distinctTheory = Language.empty.distinctConstantsTheory Set.univ := (rfl)

/-- A `ConstLang`-structure models `distinctTheory` if and only if the evaluation of the constants
is injective. -/
@[simp]
theorem model_distinctTheory_iff (M : Type w) [ConstLang.Structure M] :
    M ⊨ distinctTheory ↔ Function.Injective fun k : ℕ => (Language.empty.con k : M) := by
  rw [distinctTheory, Language.empty.model_distinctConstantsTheory Set.univ, Set.injOn_univ]

/-- The theory of pairwise distinct constants is countable. -/
theorem countable_distinctTheory : distinctTheory.Countable :=
  Set.Countable.image (Set.to_countable _) _

/-- The standard structure `StdNat` models `distinctTheory`. -/
instance stdNat_model_distinctTheory : StdNat ⊨ distinctTheory :=
  (model_distinctTheory_iff StdNat).2 fun _ _ h => StdNat.mk.inj h

/-- The theory `distinctTheory` is satisfiable in Mathlib's sense. -/
theorem distinctTheory_isSatisfiable : distinctTheory.IsSatisfiable :=
  Theory.Model.isSatisfiable StdNat

/-- The first-order formula `x₀ ≠ c_k` in one bound variable. -/
def neConstFormula (k : ℕ) : ConstLang.BoundedFormula Empty 1 :=
  ((&0).bdEqual (Language.empty.con k).term).not

/-- `neConstFormula k` is the negated equality `¬(x₀ = c_k)`. -/
theorem neConstFormula_def (k : ℕ) :
    neConstFormula k = ((&0).bdEqual (Language.empty.con k).term).not := (rfl)

/-- `neConstFormula k` holds at a 1-tuple `a` iff `a 0` differs from the interpretation of `c_k`. -/
@[simp]
theorem realize_neConstFormula_iff {M : Type w} [ConstLang.Structure M] (k : ℕ) (a : Fin 1 → M) :
    (neConstFormula k).Realize Empty.elim a ↔ a 0 ≠ (Language.empty.con k : M) := by
  simp [neConstFormula]

/-- The partial 1-type `{x₀ ≠ c_k | k : ℕ}` of an unnamed element. -/
def unnamedType : Set (ConstLang.BoundedFormula Empty 1) :=
  Set.range neConstFormula

/-- `unnamedType` is the range of `neConstFormula`. -/
theorem unnamedType_def : unnamedType = Set.range neConstFormula := (rfl)

/-- Membership in `unnamedType`. -/
@[simp]
theorem mem_unnamedType_iff {ψ : ConstLang.BoundedFormula Empty 1} :
    ψ ∈ unnamedType ↔ ∃ k : ℕ, neConstFormula k = ψ :=
  Iff.rfl

/-- The unnamed-element partial type is countable. -/
theorem countable_unnamedType : unnamedType.Countable :=
  Set.countable_range neConstFormula

/-- A 1-tuple `a` realizes `unnamedType` iff `a 0` is unequal to every constant `c_k`. -/
theorem realize_unnamedType_iff {M : Type w} [ConstLang.Structure M] (a : Fin 1 → M) :
    (∀ ψ ∈ unnamedType, ψ.Realize Empty.elim a) ↔
      ∀ k : ℕ, a 0 ≠ (Language.empty.con k : M) := by
  simp only [mem_unnamedType_iff, forall_exists_index, forall_apply_eq_imp_iff,
    realize_neConstFormula_iff]

/-- A `ConstLang`-structure omits `unnamedType` if and only if every element is the interpretation
of some constant `c_k`. -/
theorem omits_unnamedType_iff_surjective (M : Type w) [ConstLang.Structure M] :
    (∀ a : Fin 1 → M, ∃ ψ ∈ unnamedType, ¬ψ.Realize Empty.elim a) ↔
      Function.Surjective fun k : ℕ => (Language.empty.con k : M) := by
  simp only [mem_unnamedType_iff, exists_exists_eq_and, realize_neConstFormula_iff, not_ne_iff]
  exact ⟨fun h x => (h (fun _ => x)).imp fun _ hk => hk.symm,
    fun h a => (h (a 0)).imp fun _ hk => hk.symm⟩

/-- The standard structure `StdNat` omits `unnamedType`. -/
theorem stdNat_omits_unnamedType :
    ∀ a : Fin 1 → StdNat, ∃ ψ ∈ unnamedType, ¬ψ.Realize Empty.elim a :=
  (omits_unnamedType_iff_surjective StdNat).2 fun ⟨k⟩ => ⟨k, rfl⟩

/-- A `ConstLang`-structure is first-order isomorphic to `StdNat` if and only if it models
`distinctTheory` and omits `unnamedType`. -/
theorem nonempty_equiv_stdNat_iff (M : Type w) [ConstLang.Structure M] :
    Nonempty (StdNat ≃[ConstLang] M) ↔
      M ⊨ distinctTheory ∧ ∀ a : Fin 1 → M, ∃ ψ ∈ unnamedType, ¬ψ.Realize Empty.elim a := by
  rw [model_distinctTheory_iff, omits_unnamedType_iff_surjective]
  constructor
  · rintro ⟨e⟩
    have hcon : (fun k : ℕ => (Language.empty.con k : M)) = e.toEquiv ∘ StdNat.equivNat.symm := by
      ext k
      exact (e.map_constants (Language.empty.con k)).symm
    rw [hcon]
    exact ⟨(e.toEquiv.bijective.comp StdNat.equivNat.symm.bijective).injective,
      (e.toEquiv.bijective.comp StdNat.equivNat.symm.bijective).surjective⟩
  · rintro ⟨hinj, hsurj⟩
    let cBij := Equiv.ofBijective (fun k : ℕ => (Language.empty.con k : M)) ⟨hinj, hsurj⟩
    let eqv : StdNat ≃ M := StdNat.equivNat.trans cBij
    refine ⟨{ toEquiv := eqv, map_fun' := ?_, map_rel' := ?_ }⟩
    · intro n f x
      obtain ⟨⟨_, f₀⟩ | k, h⟩ :=
        (sigmaFunctionsWithConstantsEquiv (L := Language.empty) ℕ).symm.surjective ⟨n, f⟩
      · exact isEmptyElim f₀
      · rw [sigmaFunctionsWithConstantsEquiv_symm_inr] at h
        obtain ⟨rfl, rfl⟩ := Sigma.mk.inj_iff.1 h
        have h1 : @Structure.funMap ConstLang StdNat _ 0 (Language.empty.con k) x = ⟨k⟩ := by
          rw [Subsingleton.elim x default]
          rfl
        have h2 : @Structure.funMap ConstLang M _ 0 (Language.empty.con k) (eqv.toFun ∘ x) =
            (Language.empty.con k : M) := by
          rw [Subsingleton.elim (eqv.toFun ∘ x) default]
          rfl
        rw [h1, h2]
        exact Equiv.ofBijective_apply _ ⟨hinj, hsurj⟩ k
    · intro n r _
      rcases r with r | r <;> exact isEmptyElim r

/-- Every finite subset of `unnamedType` has a satisfiable conjunction with any first-order theory
`T` satisfied by `StdNat`: `StdNat` itself realizes the finite conjunction at a natural number
exceeding all constants mentioned in the finite subset. -/
theorem isSatisfiable_insert_iInf_unnamedType_of_stdNat_model (T : ConstLang.Theory) [StdNat ⊨ T]
    (s : Finset (ConstLang.BoundedFormula Empty 1))
    (hs : (s : Set (ConstLang.BoundedFormula Empty 1)) ⊆ unnamedType) :
    (insert (BoundedFormula.iInf fun ψ : s => ψ.1).exs T).IsSatisfiable := by
  classical
  choose idx hidx using fun ψ : s => mem_unnamedType_iff.1 (hs ψ.2)
  let N : ℕ := (Finset.univ.sup idx) + 1
  have hM : StdNat ⊨ insert (BoundedFormula.iInf fun ψ : s => ψ.1).exs T := by
    refine Theory.model_insert_iff.2 ⟨?_, inferInstance⟩
    rw [Sentence.Realize, Subsingleton.elim (default : Empty → StdNat) Empty.elim,
      BoundedFormula.realize_exs]
    refine ⟨fun _ => ⟨N⟩, BoundedFormula.realize_iInf.2 fun ψ => ?_⟩
    rw [← hidx ψ, realize_neConstFormula_iff, coe_con_stdNat]
    intro h
    exact Nat.ne_of_gt (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ ψ))) (StdNat.mk.inj h)
  let := hM
  exact Theory.Model.isSatisfiable StdNat

/-- **Compactness realizes `unnamedType` over every theory of `StdNat`.** Every first-order theory
`T` satisfied by `StdNat` has a nonempty model realizing `unnamedType`, containing an element
unequal to every constant `c_k`, so `Theory.IsSatisfiable` alone cannot exclude `unnamedType`. -/
theorem exists_modelType_realize_unnamedType_of_stdNat_model (T : ConstLang.Theory) [StdNat ⊨ T] :
    ∃ M : Theory.ModelType.{0, 0, 0} T, ∃ a : Fin 1 → M,
      ∀ ψ ∈ unnamedType, ψ.Realize Empty.elim a :=
  Theory.exists_modelType_realize_iff_forall_finset_isSatisfiable.2
    (isSatisfiable_insert_iInf_unnamedType_of_stdNat_model T)

/-- Even the **complete** first-order theory of `StdNat` has a model realizing `unnamedType`, which
therefore cannot be isomorphic to `StdNat`. -/
theorem exists_modelType_completeTheory_stdNat_not_equiv :
    ∃ M : Theory.ModelType.{0, 0, 0} (ConstLang.completeTheory StdNat),
      (∃ a : Fin 1 → M, ∀ ψ ∈ unnamedType, ψ.Realize Empty.elim a) ∧
        IsEmpty (StdNat ≃[ConstLang] M) := by
  obtain ⟨M, a, ha⟩ :=
    exists_modelType_realize_unnamedType_of_stdNat_model (ConstLang.completeTheory StdNat)
  refine ⟨M, ⟨a, ha⟩, ⟨fun e => ?_⟩⟩
  obtain ⟨-, homit⟩ := (nonempty_equiv_stdNat_iff M).1 ⟨e⟩
  obtain ⟨ψ, hψ, hψa⟩ := homit a
  exact hψa (ha ψ hψ)

/-- Every **finite** subset of `unnamedType` is isolated by a first-order formula modulo
`distinctTheory`, demonstrating that the finiteness hypothesis in
`Theory.exists_isolating_iff_of_finite` is essential. -/
theorem exists_isolating_of_finite_subset_unnamedType
    {p : Set (ConstLang.BoundedFormula Empty 1)} (hp : p.Finite) (hsub : p ⊆ unnamedType) :
    ∃ φ : ConstLang.BoundedFormula Empty 1,
      (insert φ.exs distinctTheory).IsSatisfiable ∧ ∀ ψ ∈ p, distinctTheory ⊨ᵇ (φ.imp ψ).alls := by
  obtain ⟨M, a, ha⟩ := exists_modelType_realize_unnamedType_of_stdNat_model distinctTheory
  exact (Theory.exists_isolating_iff_of_finite hp).2 ⟨M, a, fun ψ hψ => ha ψ (hsub hψ)⟩

/-- Every finitary formula over `L[[γ]]` mentions only finitely many of the adjoined constants. -/
private theorem finite_constantSupport_toOmega {L : Language} {γ α : Type*} :
    ∀ {n : ℕ} (φ : L[[γ]].BoundedFormula α n), φ.toOmega.constantSupport.Finite
  | _, .falsum => by simp [BoundedFormula.toInf_falsum]
  | _, .equal t₁ t₂ => by
    simp [BoundedFormula.toInf_equal, t₁.finite_constantSupport, t₂.finite_constantSupport]
  | _, .rel R ts => by
    simp [BoundedFormula.toInf_rel, Set.finite_iUnion fun i => (ts i).finite_constantSupport]
  | _, .imp φ₁ φ₂ => by
    simp [BoundedFormula.toInf_imp, finite_constantSupport_toOmega φ₁,
      finite_constantSupport_toOmega φ₂]
  | _, .all φ => by
    simp [BoundedFormula.toInf_all, finite_constantSupport_toOmega φ]

private theorem injective_update_of_forall_ne {M : Type*} {e : ℕ → M}
    (hinj : Function.Injective e) {N : ℕ} {x : M} (hx : ∀ k : ℕ, x ≠ e k) :
    Function.Injective (Function.update e N x) := by
  intro i j hij
  by_cases hi : i = N <;> by_cases hj : j = N
  · exact hi.trans hj.symm
  · rw [hi, Function.update_self, Function.update_of_ne hj] at hij
    exact (hx j hij).elim
  · rw [Function.update_of_ne hi, hj, Function.update_self] at hij
    exact (hx i hij.symm).elim
  · rw [Function.update_of_ne hi, Function.update_of_ne hj] at hij
    exact hinj hij

/-- Reinterpreting a fresh constant outside the support of `φ` at an unnamed witness preserves
`distinctTheory` and `φ` while falsifying `x₀ ≠ c_N`. -/
private theorem not_isolating_of_witness {M : Type*} [Language.empty.Structure M]
    {φ : ConstLang.BoundedFormula Empty 1} {e : ℕ → M} (hinj : Function.Injective e)
    {a : Fin 1 → M}
    (ha : @BoundedFormula.Realize ConstLang M
      (@withConstantsStructure Language.empty M _ ℕ (constantsOn.structure e))
      Empty 1 φ Empty.elim a)
    (hane : ∀ k : ℕ, a 0 ≠ e k)
    (himp : ∀ ψ ∈ unnamedType, distinctTheory ⊨ᵇ (φ.imp ψ).alls) : False := by
  obtain ⟨b, hb⟩ := (finite_constantSupport_toOmega φ).bddAbove
  let N : ℕ := b + 1
  have hN : N ∉ φ.toOmega.constantSupport := fun h => Nat.not_succ_le_self b (hb h)
  let : (constantsOn ℕ).Structure M := constantsOn.structure (Function.update e N (a 0))
  have hMS' : M ⊨ distinctTheory := (model_distinctTheory_iff M).2
    (by simpa only [coe_con_constantsOn_structure] using injective_update_of_forall_ne hinj hane)
  have ha' : φ.Realize Empty.elim a := by
    have hω := (@BoundedFormula.realize_toInf ConstLang ℕ Empty M
      (@withConstantsStructure Language.empty M _ ℕ (constantsOn.structure e))
      1 φ Empty.elim a).2 ha
    have hω' := (BoundedFormulaInf.realize_congr_of_eqOn_constantSupport
      (L := Language.empty) (M := M) (e := e) (e' := Function.update e N (a 0)) φ.toOmega
      (fun k hk => (Function.update_of_ne (ne_of_mem_of_not_mem hk hN) (a 0) e).symm)
      Empty.elim a).1 hω
    exact (BoundedFormula.realize_toInf φ Empty.elim a).1 hω'
  have : Nonempty M := ⟨a 0⟩
  let := hMS'
  have hNne := (Sentence.realize_alls (φ.imp (neConstFormula N))).1
    ((himp (neConstFormula N) ⟨N, rfl⟩).realize_sentence M) a
  have hcontra := (realize_neConstFormula_iff N a).1 (BoundedFormula.realize_imp.1 hNne ha')
  rw [coe_con_constantsOn_structure, Function.update_self] at hcontra
  exact hcontra rfl

/-- **`unnamedType` is not isolated modulo `distinctTheory`.** Any candidate isolating formula `φ`
mentions only finitely many constants, so in a model where `a` witnesses `φ` and avoids every
constant, a fresh constant `c_N` outside the support of `φ` can be reinterpreted as `a 0`,
preserving `distinctTheory` and `φ` while falsifying `x₀ ≠ c_N`. -/
theorem not_exists_isolating_unnamedType :
    ¬∃ φ : ConstLang.BoundedFormula Empty 1,
      (insert φ.exs distinctTheory).IsSatisfiable ∧
        ∀ ψ ∈ unnamedType, distinctTheory ⊨ᵇ (φ.imp ψ).alls := by
  rintro ⟨φ, hsat, himp⟩
  obtain ⟨M⟩ := hsat
  have hMT : M ⊨ distinctTheory := M.is_model.mono (Set.subset_insert _ _)
  have hφ : M ⊨ φ.exs := M.is_model.realize_of_mem _ (Set.mem_insert _ _)
  rw [Sentence.Realize, Subsingleton.elim (default : Empty → M) Empty.elim,
    BoundedFormula.realize_exs] at hφ
  obtain ⟨a, ha⟩ := hφ
  let := hMT
  have hane (k : ℕ) : a 0 ≠ (Language.empty.con k : M) := by
    have hk := (Sentence.realize_alls (φ.imp (neConstFormula k))).1
      ((himp (neConstFormula k) ⟨k, rfl⟩).realize_sentence M) a
    exact (realize_neConstFormula_iff k a).1 (BoundedFormula.realize_imp.1 hk ha)
  have hinj := (model_distinctTheory_iff M).1 hMT
  have heq := @withConstantsStructure_reduct_eq Language.empty ℕ M inferInstance
  let : Language.empty.Structure M := (Language.empty.lhomWithConstants ℕ).reduct M
  exact not_isolating_of_witness hinj (heq.symm ▸ ha) hane himp

/-- Over the complete theory of `StdNat`, non-isolation of `unnamedType` also follows directly from
`Theory.IsComplete.exists_isolating_iff_realized_in_every_countable_model`, since `StdNat` itself is
a countable model omitting `unnamedType`. -/
theorem not_exists_isolating_unnamedType_completeTheory :
    ¬∃ φ : ConstLang.BoundedFormula Empty 1,
      (insert φ.exs (ConstLang.completeTheory StdNat)).IsSatisfiable ∧
        ∀ ψ ∈ unnamedType, ConstLang.completeTheory StdNat ⊨ᵇ (φ.imp ψ).alls := by
  have hcomp : (ConstLang.completeTheory StdNat).IsComplete :=
    (completeTheory.isMaximal ConstLang StdNat).isComplete
  rw [hcomp.exists_isolating_iff_realized_in_every_countable_model.{0, 0, 0}]
  intro hall
  obtain ⟨a, ha⟩ := hall StdNat
  obtain ⟨ψ, hψ, hψa⟩ := stdNat_omits_unnamedType a
  exact hψa (ha ψ hψ)

/-- **Applying the first-order omitting types theorem.** In every universe `w`, `distinctTheory` has
a countable nonempty model `M : Type w` omitting `unnamedType`; every such model is first-order
isomorphic to `StdNat`. -/
theorem exists_countable_model_omitting_unnamedType :
    ∃ (M : Type w) (_ : ConstLang.Structure M), Countable M ∧ Nonempty M ∧
      M ⊨ distinctTheory ∧
      (∀ a : Fin 1 → M, ∃ ψ ∈ unnamedType, ¬ψ.Realize Empty.elim a) ∧
      Nonempty (StdNat ≃[ConstLang] M) := by
  obtain ⟨M, S, hMc, hMne, hMT, hMo⟩ :=
    Theory.exists_countable_model_omitting.{0, 0, w} distinctTheory_isSatisfiable
      (fun _ : Unit => unnamedType) (fun _ => not_exists_isolating_unnamedType)
  let := S
  exact ⟨M, S, hMc, hMne, hMT, hMo (), (nonempty_equiv_stdNat_iff M).2 ⟨hMT, hMo ()⟩⟩

/-- By contrast, the singleton partial 1-type `{x₀ = c_k}` naming the `k`-th constant is realized in
every model of `distinctTheory` and therefore isolated modulo `distinctTheory`. -/
def namedType (k : ℕ) : Set (ConstLang.BoundedFormula Empty 1) :=
  {(&0).bdEqual (Language.empty.con k).term}

/-- `namedType k` is the singleton `{x₀ = c_k}`. -/
theorem namedType_def (k : ℕ) :
    namedType k = {(&0).bdEqual (Language.empty.con k).term} := (rfl)

/-- Membership in `namedType k`. -/
@[simp]
theorem mem_namedType_iff {k : ℕ} {ψ : ConstLang.BoundedFormula Empty 1} :
    ψ ∈ namedType k ↔ ψ = (&0).bdEqual (Language.empty.con k).term :=
  Set.mem_singleton_iff

/-- Every structure for `ConstLang` realizes `namedType k` at the constant `c_k`. -/
theorem exists_realize_namedType (M : Type w) [ConstLang.Structure M] (k : ℕ) :
    ∃ a : Fin 1 → M, ∀ ψ ∈ namedType k, ψ.Realize Empty.elim a := by
  refine ⟨fun _ => (Language.empty.con k : M), ?_⟩
  rintro _ rfl
  simp

/-- Because `namedType k` is realized in every countable nonempty model of `distinctTheory`,
`Theory.exists_isolating_of_realized_in_every_countable_model` concludes that it is isolated by a
first-order formula modulo `distinctTheory`. -/
theorem exists_isolating_namedType (k : ℕ) :
    ∃ φ : ConstLang.BoundedFormula Empty 1,
      (insert φ.exs distinctTheory).IsSatisfiable ∧
        ∀ ψ ∈ namedType k, distinctTheory ⊨ᵇ (φ.imp ψ).alls :=
  Theory.exists_isolating_of_realized_in_every_countable_model.{0, 0, 0}
    distinctTheory_isSatisfiable fun M _ _ _ _ => exists_realize_namedType M k

-- Infinitary counterpart in the first-order image fragment: a partial type realized in every
-- countable nonempty model of a satisfiable theory is isolated in that fragment.
example (k : ℕ) :
    Theoryω.IsolatesIn (Fragment.firstOrder ConstLang)
      (BoundedFormula.toOmega '' distinctTheory)
      (BoundedFormula.toOmega '' namedType k) := by
  refine Theoryω.isolatesIn_of_realized_in_every_countable_model.{0, 0, 0}
    (T := BoundedFormula.toOmega '' distinctTheory)
    (p := BoundedFormula.toOmega '' namedType k)
    Fragment.firstOrder_countable Fragment.formationClosed_firstOrder
    (fun _ ⟨φ, _, hφ⟩ => hφ ▸ Fragment.toOmega_mem_firstOrder φ)
    (Theoryω.isSatisfiable_image_toOmega_iff.2 distinctTheory_isSatisfiable)
    (fun _ ⟨ψ, _, hψ⟩ => hψ ▸ Fragment.toOmega_mem_firstOrder ψ) ?_
  intro M instS _ _ _ ho
  let := instS
  obtain ⟨a, ha⟩ := exists_realize_namedType M k
  obtain ⟨_, ⟨ψ, hψ, rfl⟩, hψa⟩ := omitsType_iff.1 ho a
  exact hψa ((BoundedFormula.realize_toInf ψ Empty.elim a).2 (ha ψ hψ))

end TauCeti.DistinctConstantsOmitting
