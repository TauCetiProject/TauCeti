/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.ConstantInstances
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Projecting finite sets of instances

A finite set of instances of members of a formation-closed fragment defines a formula of the
fragment in any prescribed tuple of constants. The other constants are existentially quantified.
The tuple need not be injective: equalities between its coordinates ensure that a realizing
tuple extends to a consistent interpretation of the constants. This is the finite-parameter
elimination used to refute non-isolated types in the omitting types theorem.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, Chapter 4.
-/

public section

universe u v w wγ

namespace TauCeti

/-- A finite family of finite tuples in `γ`, together with one more tuple, factor through a single
injective enumeration `b : Fin m ↪ γ`: each entry of each tuple is `b` of some index. -/
theorem exists_embedding_fin_comp_eq {γ : Type*} {ι : Type*} [Finite ι] {k : ι → ℕ}
    (d : ∀ x, Fin (k x) → γ) {n : ℕ} (c : Fin n → γ) :
    ∃ (m : ℕ) (b : Fin m ↪ γ) (f : Fin n → Fin m) (g : ∀ x, Fin (k x) → Fin m),
      (∀ i, b (f i) = c i) ∧ ∀ x i, b (g x i) = d x i := by
  let F : Set γ := Set.range c ∪ ⋃ x, Set.range (d x)
  have hF : F.Finite :=
    (Set.finite_range c).union (Set.finite_iUnion fun x => Set.finite_range (d x))
  obtain ⟨m, b, hb⟩ := hF.fin_embedding
  have hc (i : Fin n) : ∃ j, b j = c i := by
    rw [← Set.mem_range, hb]
    exact Or.inl ⟨i, rfl⟩
  have hd' (x : ι) (i : Fin (k x)) : ∃ j, b j = d x i := by
    rw [← Set.mem_range, hb]
    exact Or.inr (Set.mem_iUnion.2 ⟨x, i, rfl⟩)
  choose f hf using hc
  choose g hg using hd'
  exact ⟨m, b, f, g, hf, hg⟩

end TauCeti

namespace FirstOrder.Language.Fragment.FormationClosed

open BoundedFormulaInf

variable {L : FirstOrder.Language.{u, v}} {A : Fragment L} {γ : Type wγ}

/-- A finite set of instances can be projected onto any tuple of constants by a formula in the
fragment. In every nonempty structure, this formula holds at `a` exactly when the constants can
be interpreted so that the prescribed tuple has value `a` and all the instances hold. Repeated
constants in the prescribed tuple are allowed. -/
theorem exists_formula_iff_exists_constants (hA : A.FormationClosed)
    {σ : L[[γ]].Theoryω} (hσ : σ.Finite) (hσA : σ ⊆ A.instances γ)
    {n : ℕ} (c : Fin n → γ) :
    ∃ φ : L.BoundedFormulaω Empty n, (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A ∧
      ∀ (M : Type w) [L.Structure M] [Nonempty M] (a : Fin n → M),
        φ.Realize Empty.elim a ↔ ∃ e : γ → M, e ∘ c = a ∧
          (letI := constantsOn.structure e; σ.Model M) := by
  classical
  let := hσ.fintype
  choose k χ d hχ hd using fun x : σ => mem_instances.1 (hσA x.property)
  -- Enumerate all constants in the instances and in the prescribed tuple without repetitions.
  obtain ⟨m, b, f, g, hf, hg⟩ := TauCeti.exists_embedding_fin_comp_eq d c
  -- The last slots hold one value for each distinct constant; link the first slots to them.
  -- In particular, repeated entries of `c` must have equal values.
  let ψ (x : σ) : L.BoundedFormulaω Empty (n + m) :=
    (χ x).mapBound (Fin.natAdd n ∘ g x)
  let eqs (i : Fin n) : L.BoundedFormulaω Empty (n + m) :=
    equal (Term.var (Sum.inr (Fin.castAdd m i)))
      (Term.var (Sum.inr (Fin.natAdd n (f i))))
  let l := (Finset.univ.toList.map ψ) ++ (Finset.univ.toList.map eqs)
  let θ : L.BoundedFormulaω Empty (n + m) := l.foldr (· ⊓ ·) ⊤
  have hθ : (⟨n + m, θ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A := by
    apply hA.foldr_inf_mem
    intro φ hφ
    simp only [l, List.mem_append, List.mem_map, Finset.mem_toList, Finset.mem_univ,
      true_and] at hφ
    rcases hφ with ⟨x, rfl⟩ | ⟨i, rfl⟩
    · exact hA.mapBound_mem _ (hχ x)
    · exact hA.atomic_mem (.equal _ _)
  refine ⟨θ.exsLast, hA.exsLast_mem hθ, fun M _ _ a => ?_⟩
  have hθr (z : Fin m → M) : θ.Realize Empty.elim (Fin.append a z) ↔
      (∀ x : σ, (χ x).Realize Empty.elim (z ∘ g x)) ∧ ∀ i, a i = z (f i) := by
    simp only [θ, realize_foldr_inf, l, List.forall_mem_append, List.forall_mem_map,
      Finset.mem_toList, Finset.mem_univ, forall_const, ψ, eqs, realize_mapBound,
      realize_equal, Term.realize_var, Sum.elim_inr, Function.comp_def,
      Fin.append_left, Fin.append_right]
  -- Existential witnesses give values on the enumerated constants. Extend them arbitrarily
  -- elsewhere; conversely, restrict any interpretation of the constants to this enumeration.
  rw [realize_exsLast]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨hzχ, hza⟩ := (hθr z).1 hz
    let e : γ → M := Function.extend b z (fun _ => Classical.arbitrary M)
    have he (j : Fin m) : e (b j) = z j := b.injective.extend_apply _ _ j
    let := constantsOn.structure e
    refine ⟨e, funext fun i => ?_, Theoryω.model_iff.2 fun δ hδ => ?_⟩
    · exact (congrArg e (hf i)).symm.trans ((he _).trans (hza i).symm)
    · let x : σ := ⟨δ, hδ⟩
      have hδ' : (χ x).instConstants (d x) = δ := hd x
      rw [← hδ', SentenceInf.realize_def, realize_instConstants_constantsOn]
      have hed : e ∘ d x = z ∘ g x := funext fun i =>
        (congrArg e (hg x i)).symm.trans (he _)
      rw [hed]
      exact hzχ x
  · rintro ⟨e, hec, heσ⟩
    refine ⟨e ∘ b, (hθr _).2 ⟨fun x => ?_, fun i => ?_⟩⟩
    · have hed : (e ∘ b) ∘ g x = e ∘ d x := funext fun i => congrArg e (hg x i)
      rw [hed]
      exact heσ.realize_of_instConstants_mem (hd x ▸ x.property)
    · exact (congrFun hec i).symm.trans (congrArg e (hf i)).symm

end FirstOrder.Language.Fragment.FormationClosed
