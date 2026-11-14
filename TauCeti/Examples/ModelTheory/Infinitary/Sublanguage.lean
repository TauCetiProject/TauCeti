/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.Infinitary.Sublanguage
import TauCeti.ModelTheory.Infinitary.SmallPresentation
import TauCeti.ModelTheory.Infinitary.Satisfiability

/-!
# Regression examples: symbol-sublanguage expansions and generated sublanguages

These examples exercise `expandSymbStructure`, symbol locality across expansions, and the
generated symbol sublanguages of a single sentence and of a countable set of sentences from a
downstream module, through public statements only:

* **Relational expansion on `Empty` without `[Nonempty]`**: over an uncountable relational
  language in `Language.{1, 1}`, any sublanguage structure on `Empty` expands via
  `expandSymbStructure`, gives `IsExpansionOn`, recovers the original structure under `reduct`,
  interprets out-of-sublanguage relations as empty, and preserves sentence satisfaction;
* **Nonempty-carrier expansion with function symbols**: over an uncountable algebraic language in
  `Language.{1, 1}`, expanding a sublanguage structure on `ℕ` evaluates in-sublanguage function
  terms via the sublanguage structure and transfers `L_{ω₁ω}` sentence satisfaction;
* **Symbol-locality round-trip**: restricting a structure on `Bool` to a sublanguage and
  re-expanding empties out-of-sublanguage relations while preserving satisfaction of sentences
  whose symbols lie in the sublanguage;
* **Generated countable sublanguage composed with `smallPresentation`**: over an uncountable
  language in `Language.{1, 1}`, both `φ.symbSublang` (for a sentence `φ`) and
  `BoundedFormulaInf.setSymbSublang T` (for a countable theory `T`) have countably many symbols,
  shrink to `Language.{0, 0}` via `smallPresentation`, and preserve `Theoryω.IsSatisfiable` via
  `expandSymbStructure`.
-/

open FirstOrder FirstOrder.Language

-- Over an uncountable relational language in `Language.{1, 1}`, a sublanguage structure on `Empty`
-- expands with no `Nonempty` assumption, recovers itself under `reduct`, interprets relations
-- outside `R` as empty, and preserves sentence satisfaction.
example :
    let L : Language.{1, 1} := ⟨fun _ => PEmpty.{2}, fun _ => ULift.{1} (ℕ → Bool)⟩
    ∀ (R : Set (Σ n, L.Relations n)) (S₀ : (symbSublang ∅ R).Structure Empty)
      (φ : L.Sentenceω) (hR : φ.relationsIn ⊆ R),
      letI : (symbSublang ∅ R).Structure Empty := S₀
      letI : L.Structure Empty := expandSymbStructure ∅ R Empty
      (symbSublangIncl ∅ R).IsExpansionOn Empty ∧
        (symbSublangIncl ∅ R).reduct Empty = S₀ ∧
        (∀ {n} (r : L.Relations n), (⟨n, r⟩ : Σ k, L.Relations k) ∉ R →
          ∀ xs : Fin n → Empty, ¬ Structure.RelMap r xs) ∧
        (SentenceInf.Realize φ Empty ↔
          SentenceInf.Realize (φ.restrictSymbols (F := ∅) (by simp) hR) Empty) := by
  intro L R S₀ φ hR
  let : (symbSublang ∅ R).Structure Empty := S₀
  refine ⟨isExpansionOn_expandSymbStructure ∅ R Empty, reduct_expandSymbStructure ∅ R Empty,
    fun r hr xs => expandSymbStructure_relMap_of_notMem (F := ∅) hr xs,
    SentenceInf.realize_expandSymbStructure (F := ∅) φ (by simp) hR⟩

-- Over an uncountable language with function symbols in `Language.{1, 1}`, expanding a concrete
-- sublanguage structure on `ℕ` evaluates in-sublanguage function terms via the sublanguage.
example :
    let L : Language.{1, 1} := ⟨fun _ => ULift.{1} (ℕ → Bool), fun _ => ULift.{1} (ℕ → Bool)⟩
    let f₀ : L.Functions 1 := ⟨fun _ => false⟩
    let F : Set (Σ n, L.Functions n) := {⟨1, f₀⟩}
    letI : (symbSublang F ∅).Structure ℕ :=
      { funMap := fun {n} _ xs => if h : 0 < n then xs ⟨0, h⟩ + 1 else 0
        RelMap := fun {_} r _ => r.2.elim }
    letI : L.Structure ℕ := expandSymbStructure F ∅ ℕ
    (Term.func f₀ ![Term.var ()]).realize (fun _ : Unit => (5 : ℕ)) = 6 := by
  intro L f₀ F
  let : (symbSublang F ∅).Structure ℕ :=
    { funMap := fun {n} _ xs => if h : 0 < n then xs ⟨0, h⟩ + 1 else 0
      RelMap := fun {_} r _ => r.2.elim }
  have ht : (Term.func f₀ ![Term.var ()] : L.Term Unit).functionsIn ⊆ F := by
    simp [F]
  rw [Term.realize_expandSymbStructure (R := (∅ : Set (Σ n, L.Relations n))) _ ht]
  simp [Term.restrictSymbols_func, Term.restrictSymbols_var]

-- Restricting a structure on `Bool` to a proper symbol sublanguage and re-expanding via
-- `expandSymbStructure` empties out-of-sublanguage relations while preserving sentences supported
-- in the sublanguage.
example :
    let L : Language.{0, 0} := ⟨fun _ => Empty, fun _ => Bool⟩
    let R : Set (Σ n, L.Relations n) := {⟨1, false⟩}
    let S : L.Structure Bool :=
      { funMap := fun f => f.elim
        RelMap := fun {n} r xs =>
          if h : n = 1 then r = false → xs ⟨0, by omega⟩ = true else True }
    let φ : L.Sentenceω := (BoundedFormulaInf.rel (l := 1) false ![Term.var (Sum.inr 0)]).ex
    let S' : L.Structure Bool :=
      @expandSymbStructure L ∅ R Bool ⟨S⟩ (@LHom.reduct _ _ (symbSublangIncl ∅ R) Bool S)
    @Structure.RelMap L Bool S 1 true ![true] ∧
      ¬ @Structure.RelMap L Bool S' 1 true ![true] ∧
      (@SentenceInf.Realize L ℕ φ Bool S' ↔ @SentenceInf.Realize L ℕ φ Bool S) := by
  intro L R S φ S'
  let : L.Structure Bool := S
  have hF : φ.functionsIn ⊆ (∅ : Set (Σ n, L.Functions n)) := by simp [φ]
  have hR : φ.relationsIn ⊆ R := by simp [φ, R]
  have hnot : (⟨1, true⟩ : Σ n, L.Relations n) ∉ R := by simp [R]
  refine ⟨fun h => Bool.noConfusion h, ?_, SentenceInf.realize_expandSymbStructure_reduct φ hF hR⟩
  let : (symbSublang (∅ : Set (Σ n, L.Functions n)) R).Structure Bool :=
    (symbSublangIncl ∅ R).reduct Bool
  exact expandSymbStructure_relMap_of_notMem (F := ∅) hnot ![true]

-- For any `L_{ω₁ω}` sentence `φ` over an uncountable language in `Language.{1, 1}`, its generated
-- symbol sublanguage `φ.symbSublang` has countably many function and relation symbols and shrinks
-- to `Language.{0, 0}` via `smallPresentation`.
example (φ : (Language.mk.{1, 1} (fun _ => ULift.{1} (ℕ → Bool))
    (fun _ => ULift.{1} (ℕ → Bool))).Sentenceω) :
    Countable (Σ n, φ.symbSublang.Functions n) ∧
      Countable (Σ n, φ.symbSublang.Relations n) ∧
      ∃ ψ : φ.symbSublang.smallPresentation.Sentenceω,
        φ.symbSublangIncl.onBoundedFormulaInf
          (φ.symbSublang.smallPresentationEquiv.invLHom.onBoundedFormulaInf ψ) = φ := by
  refine ⟨inferInstance, inferInstance,
    φ.symbSublang.smallPresentationEquiv.toLHom.onBoundedFormulaInf φ.toSymbSublang, ?_⟩
  rw [← LHom.comp_onBoundedFormulaInf φ.symbSublang.smallPresentationEquiv.invLHom,
    LEquiv.left_inv, LHom.id_onBoundedFormulaInf,
    BoundedFormulaInf.onBoundedFormulaInf_toSymbSublang]

-- For any countable `L_{ω₁ω}` theory `T` over an uncountable language `L : Language.{1, 1}`, its
-- generated symbol sublanguage `L₀ := BoundedFormulaInf.setSymbSublang T` is countable, the
-- restricted theory `T₀ := BoundedFormulaInf.toSetSymbSublang T` is countable, and `T` is
-- satisfiable iff `T₀` is satisfiable.
example :
    let L : Language.{1, 1} := ⟨fun _ => ULift.{1} (ℕ → Bool), fun _ => ULift.{1} (ℕ → Bool)⟩
    ∀ (T : L.Theoryω), T.Countable →
      let L₀ := BoundedFormulaInf.setSymbSublang T
      let T₀ : L₀.Theoryω := BoundedFormulaInf.toSetSymbSublang T
      Countable (Σ n, L₀.Functions n) ∧
        Countable (Σ n, L₀.Relations n) ∧
        T₀.Countable ∧
        (T.IsSatisfiable ↔ T₀.IsSatisfiable) := by
  intro L T hT
  dsimp only
  have : Countable T := hT.to_subtype
  refine ⟨inferInstance, inferInstance,
    BoundedFormulaInf.countable_toSetSymbSublang hT, ?_⟩
  simp only [Theoryω.isSatisfiable_iff, BoundedFormulaInf.toSetSymbSublang_def]
  constructor
  · rintro ⟨M, instL, hne, hM⟩
    let : (BoundedFormulaInf.setSymbSublang T).Structure M :=
      (BoundedFormulaInf.setSymbSublangIncl T).reduct M
    refine ⟨M, inferInstance, hne, Theoryω.model_iff.2 ?_⟩
    exact (SentenceInf.forall_realize_restrictSymbolsSet_iff T subset_rfl subset_rfl).2
      (Theoryω.model_iff.1 hM)
  · rintro ⟨M, instL₀, hne, hM⟩
    let : L.Structure M :=
      expandSymbStructure (BoundedFormulaInf.functionsInSet T)
        (BoundedFormulaInf.relationsInSet T) M
    refine ⟨M, inferInstance, hne, Theoryω.model_iff.2 ?_⟩
    exact (SentenceInf.forall_realize_expandSymbStructure_iff T subset_rfl subset_rfl).2
      (Theoryω.model_iff.1 hM)
