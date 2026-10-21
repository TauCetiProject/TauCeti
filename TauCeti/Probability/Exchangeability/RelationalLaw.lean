/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.FiniteSupportPerm
public import TauCeti.ModelTheory.RelationalConfiguration
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Logic.Equiv.Fintype
import TauCeti.MeasureTheory.Measure.RelationalConfiguration

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
restrictions along `Fin.val : Fin k → ℕ`. Conversely, consistent marginals are the windows of a law
over `ℕ` by Kolmogorov's extension theorem for configurations
(`TauCeti.RelationalConfiguration.exists_map_restrict_val_eq`), which is unique because a finite
measure on configurations over `ℕ` is determined by its windows
(`measure_ext_of_map_restrict_val`).

The finitely supported permutations of `ℕ` act on configurations over `ℕ` by relabelling
(`TauCeti.RelationalConfiguration.instMulActionFinitaryPerm`), and every exchangeable law on
configurations over `ℕ` is invariant under this action. Ergodicity of the action on such a law,
Mathlib's `ErgodicSMul`, is the relational counterpart of the ergodicity of exchangeable arrays.

## Main definitions

* `TauCeti.RelationalConfiguration.instMulActionFinitaryPerm` — finitely supported permutations
  of `ℕ` relabel configurations over `ℕ`;
* `TauCeti.Probability.ExchangeableRelationalLaw` — a consistent family of finite relational laws;
* `TauCeti.Probability.InfiniteExchangeableRelationalLaw` — a relabelling-invariant probability law
  on the configurations over `ℕ`;
* `TauCeti.Probability.ExchangeableRelationalLaw.IsDissociated` — restrictions to disjoint vertex
  windows are independent;
* `TauCeti.Probability.exchangeableRelationalLawEquivInfinite` — the two presentations agree.

## Main results

* `TauCeti.Probability.InfiniteExchangeableRelationalLaw.instSMulInvariantMeasureLaw` — an
  exchangeable law on configurations over `ℕ` is invariant under finitary relabelling;
* `TauCeti.Probability.exchangeableRelationalLawEquivInfinite_law_map_restrict` — the windows of
  the infinite law attached to consistent marginals are those marginals;
* `TauCeti.Probability.ExchangeableRelationalLaw.isDissociated_iff_forall_map_restrict_prod` — a
  law is dissociated exactly when the restrictions of a marginal along any two injections with
  disjoint ranges are independent.

## References

* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33--61, Section 5, for the case of graphs.
* The proof route adapts the graph case
  `TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Infinite.Basic`
  (`exchangeableGraphLawEquivInfinite`), which follows C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0, `Graphon/InfiniteLaw.lean` and
  `Graphon/InfiniteExchangeability.lean`. Here the Boolean edge coordinates of a graph are replaced
  by the Boolean atom coordinates of a configuration, and the extension of a window by `false`
  along `Fin.val` replaces the embedding of a finite graph into `ℕ`.
-/

public section

noncomputable section

open MeasureTheory

open _root_.FirstOrder (Language)

namespace TauCeti

namespace RelationalConfiguration

/-! ### Finitary relabelling of configurations over `ℕ` -/

variable {L : Language}

/-- Finitely supported permutations of `ℕ` relabel configurations over `ℕ`: `g` acts by
restriction along `g⁻¹`, so that relabelling is a left action. -/
instance instSMulFinitaryPerm : SMul FinitaryPerm (RelationalConfiguration L ℕ) :=
  ⟨fun g c => c.restrict ⇑(FinitaryPerm.toPerm g)⁻¹⟩

/-- Relabelling by `g` is restriction along `g⁻¹`. -/
theorem finitaryPerm_smul_def (g : FinitaryPerm) (c : RelationalConfiguration L ℕ) :
    g • c = c.restrict ⇑(FinitaryPerm.toPerm g)⁻¹ := (rfl)

/-- Relabelling by `g` reads every atom at its relabelling along `g⁻¹`. -/
@[simp]
theorem eval_finitaryPerm_smul (g : FinitaryPerm) (c : RelationalConfiguration L ℕ)
    (a : Atom L ℕ) : (g • c).eval a = c.eval (a.map ⇑(FinitaryPerm.toPerm g)⁻¹) := by
  rw [finitaryPerm_smul_def, eval_restrict]

/-- Finitary relabelling is a left action on configurations over `ℕ`. -/
instance instMulActionFinitaryPerm : MulAction FinitaryPerm (RelationalConfiguration L ℕ) where
  one_smul c := ext fun a => by simp [FinitaryPerm.toPerm_one, Atom.map_id]
  mul_smul g h c := ext fun a => by simp [FinitaryPerm.toPerm_mul, mul_inv_rev, ← Atom.map_comp]

/-- Each finitary relabelling of configurations over `ℕ` is measurable. -/
instance instMeasurableConstSMulFinitaryPerm :
    MeasurableConstSMul FinitaryPerm (RelationalConfiguration L ℕ) :=
  ⟨fun _ => measurable_restrict _⟩

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

/-! ### Dissociation -/

/-- An exchangeable relational law is **dissociated** when restrictions to disjoint vertex windows
are independent: the level-`(k + l)` marginal, pushed to the pair of configurations it induces on
the first `k` and on the last `l` vertices, is the product of the level-`k` and level-`l`
marginals. -/
def IsDissociated : Prop :=
  ∀ k l : ℕ,
    (μ.law (k + l)).map (fun c => (c.restrict (Fin.castAdd l), c.restrict (Fin.natAdd k))) =
      (μ.law k).prod (μ.law l)

/-- The defining identity of a dissociated law. -/
theorem isDissociated_iff :
    μ.IsDissociated ↔ ∀ k l : ℕ,
      (μ.law (k + l)).map (fun c => (c.restrict (Fin.castAdd l), c.restrict (Fin.natAdd k))) =
        (μ.law k).prod (μ.law l) := (Iff.rfl)

/-- **Dissociated laws are independent on any two disjoint windows**: the restrictions of the
level-`n` marginal along two injections with disjoint ranges are independent, with the level-`k`
and level-`l` marginals as laws. -/
theorem IsDissociated.map_restrict_prod {μ : ExchangeableRelationalLaw L} (hμ : μ.IsDissociated)
    {k l n : ℕ} {f : Fin k → Fin n} {g : Fin l → Fin n} (hf : Function.Injective f)
    (hg : Function.Injective g) (hfg : ∀ i j, f i ≠ g j) :
    (μ.law n).map (fun c => (c.restrict f, c.restrict g)) = (μ.law k).prod (μ.law l) := by
  let e : Fin (k + l) ↪ Fin n := ⟨Fin.append f g, Fin.append_injective_iff.2 ⟨hf, hg, hfg⟩⟩
  -- Merge the two injections into one; both windows are read off the merged window along `e`,
  -- along which the level-`n` marginal restricts to the level-`(k + l)` marginal.
  have hwin : (fun c : RelationalConfiguration L (Fin n) => (c.restrict f, c.restrict g)) =
      (fun c => (c.restrict (Fin.castAdd l), c.restrict (Fin.natAdd k))) ∘ restrict ⇑e := by
    funext c
    simp only [Function.comp_apply, ← restrict_comp]
    congr 2 <;> funext i
    · exact (Fin.append_left f g i).symm
    · exact (Fin.append_right f g i).symm
  rw [hwin, ← Measure.map_map ((measurable_restrict _).prodMk (measurable_restrict _))
    (measurable_restrict _), μ.consistent, hμ k l]

/-- **Dissociation on arbitrary disjoint windows.** A law is dissociated exactly when the
restrictions of every marginal along any two injections with disjoint ranges are independent,
with the smaller marginals as laws. -/
theorem isDissociated_iff_forall_map_restrict_prod :
    μ.IsDissociated ↔ ∀ (k l n : ℕ) (f : Fin k → Fin n) (g : Fin l → Fin n),
      Function.Injective f → Function.Injective g → (∀ i j, f i ≠ g j) →
        (μ.law n).map (fun c => (c.restrict f, c.restrict g)) = (μ.law k).prod (μ.law l) :=
  ⟨fun hμ _ _ _ _ _ hf hg hfg => hμ.map_restrict_prod hf hg hfg, fun h k l =>
    h k l (k + l) _ _ (Fin.castAdd_injective k l) (Fin.natAdd_injective l k) fun i j => by
      simp [Fin.ext_iff]; omega⟩

/-! ### Extension of the marginals to `ℕ` -/

variable [∀ n, Countable (L.Relations n)]

/-- The marginals are consistent under the inclusions `Fin n → Fin (n + 1)`, so they are the
windows of a probability law on configurations over `ℕ`. -/
private theorem exists_map_restrict_val_eq_law :
    ∃ ν : Measure (RelationalConfiguration L ℕ), IsProbabilityMeasure ν ∧
      ∀ n, ν.map (restrict (Fin.val : Fin n → ℕ)) = μ.law n :=
  exists_map_restrict_val_eq fun _ => μ.consistent Fin.castSuccEmb

/-- The law on configurations over `ℕ` extending the marginals. -/
private def extensionLaw : Measure (RelationalConfiguration L ℕ) :=
  μ.exists_map_restrict_val_eq_law.choose

private instance : IsProbabilityMeasure μ.extensionLaw :=
  μ.exists_map_restrict_val_eq_law.choose_spec.1

/-- The windows of the extension are the marginals. -/
private theorem extensionLaw_map_restrict (n : ℕ) :
    μ.extensionLaw.map (restrict Fin.val) = μ.law n :=
  μ.exists_map_restrict_val_eq_law.choose_spec.2 n

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

/-- An exchangeable law on configurations over `ℕ` is invariant under finitary relabelling. -/
instance instSMulInvariantMeasureLaw (μ : InfiniteExchangeableRelationalLaw L) :
    SMulInvariantMeasure FinitaryPerm (RelationalConfiguration L ℕ) μ.law :=
  ⟨fun g s hs => by
    have hsmul : (fun c : RelationalConfiguration L ℕ => g • c) =
        restrict ⇑(FinitaryPerm.toPerm g)⁻¹ := funext (finitaryPerm_smul_def g)
    rw [← Measure.map_apply (measurable_const_smul g) hs, hsmul, μ.exchangeable]⟩

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
