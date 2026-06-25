import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Basic exchangeability definitions

This file starts the Layer 0 exchangeability API: finite-dimensional block laws of a
process, prefix laws, path laws, finite exchangeability, full exchangeability, and
contractability.  The definitions are intentionally hypothesis-light; measurability
hypotheses enter only in lemmas that compose `Measure.map`s.

These declarations follow the roadmap signatures in
`TauCetiRoadmap/Exchangeability/README.md` and
`TauCetiRoadmap/Exchangeability/Targets.lean`, Layer 0.
-/

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α β ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- The finite-dimensional law of a process along an index selection `k`. -/
def finiteBlockLaw (μ : Measure Ω) (X : ℕ → Ω → α) (k : ι → ℕ) : Measure (ι → α) :=
  μ.map fun ω i => X (k i) ω

/-- The law of the first `n` coordinates of a process. -/
def prefixLaw (μ : Measure Ω) (X : ℕ → Ω → α) (n : ℕ) : Measure (Fin n → α) :=
  finiteBlockLaw μ X fun i : Fin n => i.val

/-- The law of the whole process as a measure on path space. -/
def pathLaw (μ : Measure Ω) (X : ℕ → Ω → α) : Measure (ℕ → α) :=
  finiteBlockLaw μ X id

/-- Projection from path space to the first `n` coordinates. -/
def prefixProj (α : Type*) (n : ℕ) (x : ℕ → α) : Fin n → α :=
  fun i => x i.val

/-- The left shift on one-sided path space. -/
def shift (α : Type*) (x : ℕ → α) : ℕ → α :=
  fun n => x (n + 1)

/-- Finite exchangeability at `n`: the first `n` coordinates have permutation-invariant law. -/
def ExchangeableAt (μ : Measure Ω) (X : ℕ → Ω → α) (n : ℕ) : Prop :=
  ∀ σ : Equiv.Perm (Fin n),
    finiteBlockLaw μ X (fun i : Fin n => (σ i).val) = prefixLaw μ X n

/-- Finite exchangeability at every length. -/
def Exchangeable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ n, ExchangeableAt μ X n

/-- Full exchangeability: the path law is invariant under every permutation of `ℕ`. -/
def FullyExchangeable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ π : Equiv.Perm ℕ, finiteBlockLaw μ X π = pathLaw μ X

/-- Contractability, or spreadability: finite-dimensional laws are invariant under strictly
increasing finite subsequences. -/
def Contractable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ (m : ℕ) (k : Fin m → ℕ), StrictMono k → finiteBlockLaw μ X k = prefixLaw μ X m

@[simp]
theorem finiteBlockLaw_apply (μ : Measure Ω) (X : ℕ → Ω → α) (k : ι → ℕ) :
    finiteBlockLaw μ X k = μ.map (fun ω i => X (k i) ω) :=
  rfl

@[simp]
theorem prefixLaw_apply (μ : Measure Ω) (X : ℕ → Ω → α) (n : ℕ) :
    prefixLaw μ X n = finiteBlockLaw μ X (fun i : Fin n => i.val) :=
  rfl

@[simp]
theorem pathLaw_apply (μ : Measure Ω) (X : ℕ → Ω → α) :
    pathLaw μ X = finiteBlockLaw μ X id :=
  rfl

omit [MeasurableSpace α] in
@[simp]
theorem prefixProj_apply (n : ℕ) (x : ℕ → α) (i : Fin n) :
    prefixProj α n x i = x i.val :=
  rfl

omit [MeasurableSpace α] in
@[simp]
theorem shift_apply (x : ℕ → α) (n : ℕ) : shift α x n = x (n + 1) :=
  rfl

/-- The prefix projection is measurable. -/
theorem measurable_prefixProj (n : ℕ) : Measurable (prefixProj α n) := by
  unfold prefixProj
  measurability

/-- The one-sided path-space shift is measurable. -/
theorem measurable_shift : Measurable (shift α) := by
  unfold shift
  measurability

/-- The prefix law is the pushforward of the path law by `prefixProj`. -/
theorem map_prefixProj_pathLaw (μ : Measure Ω) {X : ℕ → Ω → α}
    (hX : ∀ i, Measurable (X i)) (n : ℕ) :
    (pathLaw μ X).map (prefixProj α n) = prefixLaw μ X n := by
  rw [pathLaw, prefixLaw, finiteBlockLaw, finiteBlockLaw]
  rw [Measure.map_map]
  · rfl
  · exact measurable_prefixProj n
  · exact measurable_pi_lambda (fun ω => fun i => X i ω) fun i => hX i

/-- A coordinatewise measurable map sends block laws to block laws. -/
theorem map_finiteBlockLaw (μ : Measure Ω) {X : ℕ → Ω → α} (k : ι → ℕ)
    {f : α → β} [MeasurableSpace β] (hf : Measurable f) (hX : ∀ i, Measurable (X i)) :
    (finiteBlockLaw μ X k).map (fun x : ι → α => fun i => f (x i)) =
      finiteBlockLaw μ (fun n ω => f (X n ω)) k := by
  rw [finiteBlockLaw, finiteBlockLaw]
  rw [Measure.map_map]
  · rfl
  · exact measurable_pi_lambda (fun x : ι → α => fun i => f (x i)) fun i =>
      hf.comp (measurable_pi_apply i)
  · exact measurable_pi_lambda (fun ω => fun i => X (k i) ω) fun i => hX (k i)

/-- A coordinatewise measurable map sends prefix laws to prefix laws. -/
theorem map_prefixLaw (μ : Measure Ω) {X : ℕ → Ω → α}
    {f : α → β} [MeasurableSpace β] (hf : Measurable f) (hX : ∀ i, Measurable (X i))
    (n : ℕ) :
    (prefixLaw μ X n).map (fun x : Fin n → α => fun i => f (x i)) =
      prefixLaw μ (fun n ω => f (X n ω)) n :=
  map_finiteBlockLaw μ (fun i : Fin n => i.val) hf hX

theorem Exchangeable.exchangeableAt {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : Exchangeable μ X) (n : ℕ) : ExchangeableAt μ X n :=
  h n

theorem ExchangeableAt.permute {μ : Measure Ω} {X : ℕ → Ω → α} {n : ℕ}
    (h : ExchangeableAt μ X n) (σ : Equiv.Perm (Fin n)) :
    finiteBlockLaw μ X (fun i : Fin n => (σ i).val) = prefixLaw μ X n :=
  h σ

theorem Contractable.map {μ : Measure Ω} {X : ℕ → Ω → α} (h : Contractable μ X)
    {m : ℕ} {k : Fin m → ℕ} (hk : StrictMono k) :
    finiteBlockLaw μ X k = prefixLaw μ X m :=
  h m k hk

/-- The one-coordinate specialization of contractability. -/
theorem Contractable.map_single {μ : Measure Ω} {X : ℕ → Ω → α} (h : Contractable μ X)
    (k : Fin 1 → ℕ) :
    finiteBlockLaw μ X k = prefixLaw μ X 1 := by
  exact h.map (by
    intro i j hij
    fin_cases i
    fin_cases j
    omega)

/-- The two-coordinate specialization of contractability. -/
theorem Contractable.map_pair {μ : Measure Ω} {X : ℕ → Ω → α} (h : Contractable μ X)
    {i j : ℕ} (hij : i < j) :
    finiteBlockLaw μ X (fun r : Fin 2 => if r = 0 then i else j) = prefixLaw μ X 2 := by
  refine h.map ?_
  intro r s hrs
  fin_cases r <;> fin_cases s <;> simp_all

/-- Contractability is preserved by passing to a strictly increasing subsequence. -/
theorem Contractable.comp {μ : Measure Ω} {X : ℕ → Ω → α} (h : Contractable μ X)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    Contractable μ (fun n ω => X (φ n) ω) := by
  intro m k hk
  calc
    finiteBlockLaw μ (fun n ω => X (φ n) ω) k =
        finiteBlockLaw μ X (φ ∘ k) := rfl
    _ = prefixLaw μ X m := h.map (hφ.comp hk)
    _ = finiteBlockLaw μ (fun n ω => X (φ n) ω) (fun i : Fin m => i.val) := by
      exact (h.map (hφ.comp (Fin.val_strictMono : StrictMono (fun i : Fin m => i.val)))).symm
    _ = prefixLaw μ (fun n ω => X (φ n) ω) m := rfl

end Probability

end TauCeti
