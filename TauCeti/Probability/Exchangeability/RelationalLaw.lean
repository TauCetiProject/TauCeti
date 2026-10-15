/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Constructions.Projective
import TauCeti.MeasureTheory.Measure.ProjectiveLimit.Countable

/-!
# Exchangeable relational laws

An exchangeable random structure of a one-sorted relational language `L` on an unbounded vertex
set has two presentations.

* **Consistent finite marginals** (`ExchangeableRelationalLaw L`): a probability law on the
  relational configurations on `Fin k` for every `k`, consistent under restriction along every
  injection `Fin k ↪ Fin l`. The permutations of `Fin k` give invariance under relabelling, and the
  inclusions `Fin k ↪ Fin (k + 1)` give projectivity.
* **One invariant law on `ℕ`** (`InfiniteExchangeableRelationalLaw L`): a probability law on the
  relational configurations on `ℕ`, invariant under restriction along every permutation of `ℕ`.

The two presentations agree (`exchangeableRelationalLawEquivInfinite`) when `L` has countably
many relation symbols of each arity. From an infinite law, the marginals are its windows: the
restrictions along `Fin.val : Fin k → ℕ`. Conversely, a finite set of atoms over `ℕ` involves
finitely many vertices, so the marginals prescribe the law of every finite set of atom coordinates.
Kolmogorov's extension theorem on the countable product of these Boolean coordinates provides the
infinite law; it is unique because a finite measure on configurations over `ℕ` is determined by its
windows (`measure_ext_of_map_restrict_val`).

## Main definitions

* `TauCeti.Probability.ExchangeableRelationalLaw` — a consistent family of finite relational laws;
* `TauCeti.Probability.InfiniteExchangeableRelationalLaw` — a relabelling-invariant probability law
  on the configurations over `ℕ`;
* `TauCeti.Probability.exchangeableRelationalLawEquivInfinite` — the two presentations agree.

## Main results

* `TauCeti.RelationalConfiguration.measure_ext_of_forall_finset` — a finite measure on
  configurations is determined by the laws of its values at finite sets of atoms;
* `TauCeti.RelationalConfiguration.map_restrict_eq_of_forall_finset` — the restriction of a
  finite measure along a vertex map is determined by the laws of the finite sets of atoms that are
  relabelled from the source;
* `TauCeti.RelationalConfiguration.measure_ext_of_map_restrict_val` — a finite measure on
  configurations over `ℕ` is determined by its windows;
* `TauCeti.Probability.exchangeableRelationalLawEquivInfinite_law_map_restrict` — the windows of
  the infinite law attached to consistent marginals are those marginals.

## References

* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33--61, Section 5, for the case of graphs.
-/

public section

noncomputable section

open MeasureTheory

open _root_.FirstOrder (Language)

namespace TauCeti

/-! ### Measures on configurations -/

namespace RelationalConfiguration

variable {L : Language} {V W : Type*}

/-- Reading off a finite set of atoms is measurable. -/
private theorem measurable_restrict_eval (J : Finset (Atom L V)) :
    Measurable fun c : RelationalConfiguration L V => J.restrict c.eval := by
  fun_prop

/-- **A finite measure on configurations is determined by its finite-dimensional laws**, the laws
of the values at finite sets of atoms. -/
theorem measure_ext_of_forall_finset {μ ν : Measure (RelationalConfiguration L V)}
    [IsFiniteMeasure μ]
    (h : ∀ J : Finset (Atom L V),
      μ.map (fun c => J.restrict c.eval) = ν.map (fun c => J.restrict c.eval)) : μ = ν := by
  have heval : Measurable fun c : RelationalConfiguration L V => c.eval :=
    measurable_pi_iff.2 measurable_eval
  -- The laws of the atom values are projective limits of the same family.
  have hcoord : μ.map (fun c => c.eval) = ν.map (fun c => c.eval) :=
    IsProjectiveLimit.unique (P := fun J => μ.map fun c => J.restrict c.eval)
      (fun J => by rw [Measure.map_map (Finset.measurable_restrict J) heval]; rfl)
      fun J => by rw [Measure.map_map (Finset.measurable_restrict J) heval]; exact (h J).symm
  have hmk : ∀ ρ : Measure (RelationalConfiguration L V), (ρ.map fun c => c.eval).map mk = ρ :=
    fun ρ => by
      have hid : (mk ∘ fun c : RelationalConfiguration L V => c.eval) = id :=
        funext fun c => ext fun a => eval_mk _ a
      rw [Measure.map_map measurable_mk heval, hid, Measure.map_id]
  rw [← hmk μ, hcoord, hmk]

/-- Two finite measures on configurations have the same restriction along a vertex map `f` as soon
as they give the same law to every finite set of atoms relabelled along `f`. -/
theorem map_restrict_eq_of_forall_finset {μ ν : Measure (RelationalConfiguration L W)}
    [IsFiniteMeasure μ] (f : V → W)
    (h : ∀ J : Finset (Atom L W), (∀ a ∈ J, ∃ b : Atom L V, b.map f = a) →
      μ.map (fun c => J.restrict c.eval) = ν.map (fun c => J.restrict c.eval)) :
    μ.map (restrict f) = ν.map (restrict f) := by
  classical
  refine measure_ext_of_forall_finset fun J => ?_
  -- Reading the atoms of `J` after restricting along `f` reads the atoms of `J.image (map f)`.
  have hread : (fun c : RelationalConfiguration L W => J.restrict (c.restrict f).eval) =
      (fun x j => x ⟨j.1.map f, Finset.mem_image_of_mem _ j.2⟩) ∘
        fun c => (J.image (Atom.map f)).restrict c.eval := by
    funext c
    ext j
    simp
  have hlaw : ∀ ρ : Measure (RelationalConfiguration L W),
      (ρ.map (restrict f)).map (fun d => J.restrict d.eval) =
        (ρ.map fun c => (J.image (Atom.map f)).restrict c.eval).map
          fun x j => x ⟨j.1.map f, Finset.mem_image_of_mem _ j.2⟩ := fun ρ => by
    rw [Measure.map_map (measurable_restrict_eval J) (measurable_restrict f),
      Measure.map_map (measurable_of_countable _) (measurable_restrict_eval _)]
    exact congrArg ρ.map hread
  refine (hlaw μ).trans ((congrArg (Measure.map _) (h _ fun a ha => ?_)).trans (hlaw ν).symm)
  obtain ⟨b, -, hb⟩ := Finset.mem_image.1 ha
  exact ⟨b, hb⟩

/-- The atoms relabelled from `Fin m` are relabelled from `Fin n` for every `n ≥ m`. -/
private theorem exists_map_val_of_le {m n : ℕ} (hmn : m ≤ n) {a : Atom L ℕ}
    (ha : ∃ b : Atom L (Fin m), b.map Fin.val = a) : ∃ b : Atom L (Fin n), b.map Fin.val = a := by
  obtain ⟨b, rfl⟩ := ha
  -- `Fin.val ∘ Fin.castLE hmn` is `Fin.val` by definition; no rewrite lemma states it.
  exact ⟨b.map (Fin.castLE hmn), by rw [← Atom.map_comp]; rfl⟩

/-- Every finite set of atoms over `ℕ` has its vertices below some bound `n`, so its atoms are
relabelled from atoms of `Fin n`. -/
private theorem exists_forall_map_val (J : Finset (Atom L ℕ)) :
    ∃ n, ∀ a ∈ J, ∃ b : Atom L (Fin n), b.map Fin.val = a := by
  classical
  induction J using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a J _ ih =>
    obtain ⟨m, hm⟩ := ih
    -- The single atom `a` has its finitely many vertices below some bound `k`.
    obtain ⟨k, hk⟩ : ∃ k, ∃ b : Atom L (Fin k), b.map Fin.val = a := by
      induction a using Atom.induction_atom with
      | h R x =>
        obtain ⟨k, hk⟩ := Finset.exists_nat_subset_range (Finset.univ.image x)
        exact ⟨k, atom R fun i => ⟨x i, Finset.mem_range.1 (hk (Finset.mem_image_of_mem _
          (Finset.mem_univ i)))⟩, by rw [Atom.map_atom]; rfl⟩
    refine ⟨max k m, fun b hb => ?_⟩
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact exists_map_val_of_le (le_max_left k m) hk
    · exact exists_map_val_of_le (le_max_right k m) (hm b hb)

/-- **A finite measure on configurations over `ℕ` is determined by its windows**, the
restrictions along `Fin.val : Fin n → ℕ`: every finite set of atoms lies in some window, where
the configuration is recovered by extending its restriction. -/
theorem measure_ext_of_map_restrict_val {μ ν : Measure (RelationalConfiguration L ℕ)}
    [IsFiniteMeasure μ]
    (h : ∀ n, μ.map (restrict (Fin.val : Fin n → ℕ)) = ν.map (restrict Fin.val)) : μ = ν := by
  refine measure_ext_of_forall_finset fun J => ?_
  obtain ⟨n, hn⟩ := exists_forall_map_val J
  -- The atoms of `J` are read off the extension of the window below `n`.
  have hread : (fun c : RelationalConfiguration L ℕ => J.restrict c.eval) =
      (fun d => J.restrict (d.extend Fin.val).eval) ∘ restrict (Fin.val : Fin n → ℕ) := by
    funext c
    ext a
    obtain ⟨b, hb⟩ := hn a a.2
    simp [← hb, Fin.val_injective]
  have hm : Measurable fun d : RelationalConfiguration L (Fin n) =>
      J.restrict (d.extend Fin.val).eval :=
    (measurable_restrict_eval J).comp (measurable_extend _)
  rw [hread, ← Measure.map_map hm (measurable_restrict _), h, Measure.map_map hm
    (measurable_restrict _)]

end RelationalConfiguration

namespace Probability

open RelationalConfiguration

variable (L : Language)

/-! ### Consistent finite marginals -/

/-- An exchangeable random structure of `L`, presented by its consistent finite marginals: a
probability law on the configurations on `Fin k` for every `k`, consistent under restriction along
every injection of vertices. -/
structure ExchangeableRelationalLaw where
  /-- The level-`k` marginal law. -/
  law : (k : ℕ) → Measure (RelationalConfiguration L (Fin k))
  /-- Every marginal is a probability measure. -/
  prob : ∀ k, IsProbabilityMeasure (law k)
  /-- Consistency under restriction along every injection of vertices. -/
  consistent : ∀ {k l : ℕ} (f : Fin k ↪ Fin l), (law l).map (restrict ⇑f) = law k

attribute [simp] ExchangeableRelationalLaw.consistent

namespace ExchangeableRelationalLaw

variable {L}

instance instIsProbabilityMeasureLaw (μ : ExchangeableRelationalLaw L) (k : ℕ) :
    IsProbabilityMeasure (μ.law k) := μ.prob k

/-- A law is determined by its marginals: the remaining fields are propositions. -/
@[ext]
theorem ext {μ ν : ExchangeableRelationalLaw L} (h : ∀ k, μ.law k = ν.law k) : μ = ν := by
  cases μ
  cases ν
  congr 1
  exact funext h

variable (μ : ExchangeableRelationalLaw L)

/-- The law of the atoms in `J` under the level-`n` marginal, extended by `false` to `ℕ`. -/
private def coordLaw (n : ℕ) (J : Finset (Atom L ℕ)) : Measure (∀ _ : J, Bool) :=
  (μ.law n).map fun d => J.restrict (d.extend Fin.val).eval

private theorem measurable_restrict_eval_extend (n : ℕ) (J : Finset (Atom L ℕ)) :
    Measurable fun d : RelationalConfiguration L (Fin n) => J.restrict (d.extend Fin.val).eval :=
  (measurable_restrict_eval J).comp (measurable_extend _)

/-- The law of the atoms in `J` does not depend on the level, as long as the level bounds the
vertices of the atoms of `J`. -/
private theorem coordLaw_eq_of_le {J : Finset (Atom L ℕ)} {m n : ℕ}
    (hJ : ∀ a ∈ J, ∃ b : Atom L (Fin m), b.map Fin.val = a) (hmn : m ≤ n) :
    μ.coordLaw n J = μ.coordLaw m J := by
  -- Reading the atoms of `J` at level `n` is reading them on the window below `m`.
  have hread : (fun d : RelationalConfiguration L (Fin n) => J.restrict (d.extend Fin.val).eval) =
      (fun d : RelationalConfiguration L (Fin m) => J.restrict (d.extend Fin.val).eval) ∘
        restrict (Fin.castLEEmb hmn) := by
    funext d
    ext a
    obtain ⟨b, hb⟩ := hJ a a.2
    have hval : (b.map (Fin.castLEEmb hmn)).map Fin.val = b.map (Fin.val : Fin m → ℕ) := by
      -- `Fin.val ∘ Fin.castLEEmb hmn` is `Fin.val` by definition.
      rw [← Atom.map_comp]
      rfl
    simp only [Function.comp_apply, Finset.restrict, ← hb]
    rw [← hval, eval_extend_map Fin.val_injective, hval, eval_extend_map Fin.val_injective,
      eval_restrict]
  rw [coordLaw, coordLaw, ← μ.consistent (Fin.castLEEmb hmn),
    Measure.map_map (measurable_restrict_eval_extend m J) (measurable_restrict _), ← hread]

/-- A level bounding the vertices of the atoms in `J`. -/
private def level (J : Finset (Atom L ℕ)) : ℕ :=
  (exists_forall_map_val J).choose

private theorem level_spec (J : Finset (Atom L ℕ)) :
    ∀ a ∈ J, ∃ b : Atom L (Fin (level J)), b.map Fin.val = a :=
  (exists_forall_map_val J).choose_spec

/-- The marginals prescribe the law of every finite set of atoms. -/
private def coordFamily (J : Finset (Atom L ℕ)) : Measure (∀ _ : J, Bool) :=
  μ.coordLaw (level J) J

private instance (J : Finset (Atom L ℕ)) : IsProbabilityMeasure (μ.coordFamily J) := by
  unfold coordFamily coordLaw
  infer_instance

/-- The prescribed law of the atoms in `J` is read off any level bounding their vertices. -/
private theorem coordFamily_eq {J : Finset (Atom L ℕ)} {n : ℕ}
    (hJ : ∀ a ∈ J, ∃ b : Atom L (Fin n), b.map Fin.val = a) :
    μ.coordFamily J = μ.coordLaw n J := by
  rw [coordFamily, ← μ.coordLaw_eq_of_le (level_spec J) (le_max_left (level J) n),
    μ.coordLaw_eq_of_le hJ (le_max_right _ n)]

private theorem isProjectiveMeasureFamily_coordFamily :
    IsProjectiveMeasureFamily (α := fun _ : Atom L ℕ => Bool) μ.coordFamily := by
  intro I J hJI
  have hI := level_spec I
  rw [μ.coordFamily_eq hI, μ.coordFamily_eq fun a ha => hI a (hJI ha), coordLaw, coordLaw,
    Measure.map_map (measurable_of_countable _) (measurable_restrict_eval_extend _ I)]
  -- Restricting the atoms in `I` to `J` is restricting to `J` (`restrict₂_comp_restrict`).
  rfl

variable [∀ n, Countable (L.Relations n)]

/-- **Kolmogorov extension** of the coordinate laws prescribed by the marginals. -/
private theorem exists_isProjectiveLimit_coordFamily :
    ∃ ν : Measure (Atom L ℕ → Bool), IsProbabilityMeasure ν ∧
      IsProjectiveLimit ν μ.coordFamily :=
  TauCeti.Measure.exists_isProjectiveLimit_of_countable (X := fun _ : Atom L ℕ => Bool)
    μ.coordFamily μ.isProjectiveMeasureFamily_coordFamily

/-- The law on configurations over `ℕ` extending the marginals. -/
private def extensionLaw : Measure (RelationalConfiguration L ℕ) :=
  μ.exists_isProjectiveLimit_coordFamily.choose.map RelationalConfiguration.mk

private instance : IsProbabilityMeasure μ.extensionLaw := by
  have := μ.exists_isProjectiveLimit_coordFamily.choose_spec.1
  unfold extensionLaw
  infer_instance

/-- The atoms in `J` have the law prescribed by the marginals under the extension. -/
private theorem extensionLaw_map_restrict_eval (J : Finset (Atom L ℕ)) :
    μ.extensionLaw.map (fun c => J.restrict c.eval) = μ.coordFamily J := by
  have hread : ((fun c : RelationalConfiguration L ℕ => J.restrict c.eval) ∘
      RelationalConfiguration.mk) = J.restrict :=
    funext fun x => funext fun a => eval_mk x a
  rw [extensionLaw, Measure.map_map (measurable_restrict_eval J) measurable_mk, hread]
  exact μ.exists_isProjectiveLimit_coordFamily.choose_spec.2 J

/-- The windows of the extension are the marginals. -/
private theorem extensionLaw_map_restrict (n : ℕ) :
    μ.extensionLaw.map (restrict Fin.val) = μ.law n := by
  have hid : restrict (L := L) (Fin.val : Fin n → ℕ) ∘ extend Fin.val = id :=
    funext (restrict_extend Fin.val_injective)
  -- The marginal is the window of its own extension by `false`.
  rw [← Measure.map_id (μ := μ.law n), ← hid,
    ← Measure.map_map (measurable_restrict _) (measurable_extend _)]
  refine map_restrict_eq_of_forall_finset _ fun J hJ => ?_
  rw [extensionLaw_map_restrict_eval, coordFamily_eq _ hJ, coordLaw,
    Measure.map_map (measurable_restrict_eval J) (measurable_extend _)]
  rfl

/-- The extension is invariant under every relabelling: a window of the relabelled extension is a
restriction of a larger window along an injection of vertices. -/
private theorem extensionLaw_map_restrict_perm (σ : Equiv.Perm ℕ) :
    μ.extensionLaw.map (restrict ⇑σ) = μ.extensionLaw := by
  refine measure_ext_of_map_restrict_val fun n => ?_
  obtain ⟨m, hm⟩ := Finset.exists_nat_subset_range (Finset.univ.image fun i : Fin n => σ i)
  have hlt : ∀ i : Fin n, σ i < m := fun i =>
    Finset.mem_range.1 (hm (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  let f : Fin n ↪ Fin m :=
    ⟨fun i => ⟨σ i, hlt i⟩, fun i j hij => Fin.ext (σ.injective (Fin.mk.inj_iff.1 hij))⟩
  -- Relabelling by `σ` and taking the window below `n` is the window below `m` read along `f`.
  have hwin : restrict (L := L) (Fin.val : Fin n → ℕ) ∘ restrict ⇑σ =
      restrict ⇑f ∘ restrict Fin.val := by
    funext c
    rw [Function.comp_apply, Function.comp_apply, ← restrict_comp, ← restrict_comp]
    rfl
  rw [Measure.map_map (measurable_restrict _) (measurable_restrict _), hwin,
    ← Measure.map_map (measurable_restrict _) (measurable_restrict _),
    μ.extensionLaw_map_restrict, μ.consistent, μ.extensionLaw_map_restrict]

end ExchangeableRelationalLaw

/-! ### Invariant laws on `ℕ` -/

/-- An **exchangeable law on configurations over `ℕ`**: a probability law on the relational
configurations over `ℕ` invariant under relabelling along every permutation of `ℕ`. -/
structure InfiniteExchangeableRelationalLaw where
  /-- The law on configurations over `ℕ`. -/
  law : Measure (RelationalConfiguration L ℕ)
  /-- It is a probability measure. -/
  prob : IsProbabilityMeasure law
  /-- Invariance under every relabelling. -/
  exchangeable : ∀ σ : Equiv.Perm ℕ, law.map (restrict ⇑σ) = law

attribute [simp] InfiniteExchangeableRelationalLaw.exchangeable

namespace InfiniteExchangeableRelationalLaw

variable {L}

instance instIsProbabilityMeasureLaw (μ : InfiniteExchangeableRelationalLaw L) :
    IsProbabilityMeasure μ.law := μ.prob

/-- An exchangeable law on configurations over `ℕ` is determined by its law: the other fields are
propositions. -/
@[ext]
theorem ext {μ ν : InfiniteExchangeableRelationalLaw L} (h : μ.law = ν.law) : μ = ν := by
  cases μ
  cases ν
  congr

/-- **The windows of an exchangeable law are consistent**: restricting along an injection
`Fin k ↪ Fin l` is relabelling along a permutation of `ℕ` extending it, followed by taking the
smaller window. -/
theorem map_restrict_val_map_restrict (μ : InfiniteExchangeableRelationalLaw L) {k l : ℕ}
    (f : Fin k ↪ Fin l) :
    (μ.law.map (restrict (Fin.val : Fin l → ℕ))).map (restrict ⇑f) =
      μ.law.map (restrict Fin.val) := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (fun i : Fin k => (i : ℕ))
    (fun i => (f i : ℕ)) Fin.val_injective (Fin.val_injective.comp f.injective)
  have hwin : restrict (L := L) ⇑f ∘ restrict (Fin.val : Fin l → ℕ) =
      restrict (Fin.val : Fin k → ℕ) ∘ restrict ⇑σ := by
    funext c
    rw [Function.comp_apply, Function.comp_apply, ← restrict_comp, ← restrict_comp]
    congr 1
    funext i
    exact (hσ i).symm
  rw [Measure.map_map (measurable_restrict _) (measurable_restrict _), hwin,
    ← Measure.map_map (measurable_restrict _) (measurable_restrict _), μ.exchangeable]

end InfiniteExchangeableRelationalLaw

/-! ### The two presentations agree -/

variable [∀ n, Countable (L.Relations n)]

/-- **Consistent finite marginals are an exchangeable law on configurations over `ℕ`.** For a
language with countably many relation symbols of each arity, consistent marginals extend to a unique
relabelling-invariant law over `ℕ` whose windows are those marginals; conversely the windows of
such a law are consistent marginals. -/
def exchangeableRelationalLawEquivInfinite :
    ExchangeableRelationalLaw L ≃ InfiniteExchangeableRelationalLaw L where
  toFun μ := ⟨μ.extensionLaw, inferInstance, μ.extensionLaw_map_restrict_perm⟩
  invFun μ :=
    { law := fun _ => μ.law.map (restrict Fin.val)
      prob := fun _ => inferInstance
      consistent := μ.map_restrict_val_map_restrict }
  left_inv μ := ExchangeableRelationalLaw.ext fun k => μ.extensionLaw_map_restrict k
  right_inv _ := InfiniteExchangeableRelationalLaw.ext <| measure_ext_of_map_restrict_val fun n =>
    ExchangeableRelationalLaw.extensionLaw_map_restrict _ n

variable {L}

/-- **The windows of the extension are the marginals.** -/
@[simp]
theorem exchangeableRelationalLawEquivInfinite_law_map_restrict (μ : ExchangeableRelationalLaw L)
    (k : ℕ) :
    (exchangeableRelationalLawEquivInfinite L μ).law.map (restrict (Fin.val : Fin k → ℕ)) =
      μ.law k :=
  μ.extensionLaw_map_restrict k

/-- The marginals attached to an exchangeable law on configurations over `ℕ` are its windows. -/
@[simp]
theorem exchangeableRelationalLawEquivInfinite_symm_law (μ : InfiniteExchangeableRelationalLaw L)
    (k : ℕ) :
    ((exchangeableRelationalLawEquivInfinite L).symm μ).law k =
      μ.law.map (restrict (Fin.val : Fin k → ℕ)) :=
  (rfl)

end Probability

end TauCeti
