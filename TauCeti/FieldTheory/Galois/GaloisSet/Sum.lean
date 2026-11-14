/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Sort
public import TauCeti.FieldTheory.Galois.GaloisSet.Basic
import Mathlib.GroupTheory.Perm.Finite

/-!
# Disjoint unions and orbit decompositions of labelled Galois sets

Sums over `TauCeti.GaloisSet K n` of orbit-additive invariants — such as discriminant weights and
splitting symbols in Bhargava's mass formulas — reduce to the transitive case by induction on `n`
once one peels off the orbit of a fixed label `i₀ : Fin n` and splits the action into that
transitive orbit and its complement. This file constructs that bijection.

Two labelled Galois sets `ρ₁ : TauCeti.GaloisSet K a` and `ρ₂ : TauCeti.GaloisSet K b` glue along
any bijection `e : Fin a ⊕ Fin b ≃ Fin n` to form `TauCeti.GaloisSet.ofSum` on `Fin n`, in which
`e ∘ Sum.inl` and `e ∘ Sum.inr` are equivariant embeddings of the two summands. Conversely, by
`Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl`, every labelled Galois set leaving
`Set.range (e ∘ Sum.inl)` invariant arises uniquely in this way (`TauCeti.GaloisSet.ofSumEquiv`).

Specialised to `finSumEquivOfFinset`, which enumerates a subset `S : Finset (Fin n)` and its
complement `Sᶜ` in increasing order on each summand separately, peeling off the orbit finset
`TauCeti.GaloisSet.orbitFinset` of a chosen point `i₀ : Fin n` decomposes `TauCeti.GaloisSet K n`
into the choice of an orbit size `m ∈ [1, n]`, an `m`-element subset `S ⊆ Fin n` containing `i₀`,
a transitive Galois set on `Fin m`, and an arbitrary Galois set on `Fin (n - m)`
(`TauCeti.GaloisSet.orbitDecompositionEquiv`).

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density
  of number field discriminants*, IMRN **2007**, rnm052, §2.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN **2007**, rnm021.
-/

public section

noncomputable section

namespace TauCeti.GaloisSet

universe u

variable {K : Type u} [Field K]

section ofSum

variable {a b n : ℕ}

/-- Glue two labelled Galois sets along a bijection `e : Fin a ⊕ Fin b ≃ Fin n`. Its kernel is the
intersection of the two summands' kernels, hence open. -/
def ofSum (e : Fin a ⊕ Fin b ≃ Fin n) (ρ₁ : GaloisSet K a) (ρ₂ : GaloisSet K b) : GaloisSet K n :=
  ⟨e.permCongrHom.toMonoidHom.comp
      ((Equiv.Perm.sumCongrHom (Fin a) (Fin b)).comp (ρ₁.val.prod ρ₂.val)), by
    rw [MonoidHom.ker_comp_of_injective _ _ e.permCongrHom.injective,
      MonoidHom.ker_comp_of_injective _ _ Equiv.Perm.sumCongrHom_injective, MonoidHom.ker_prod]
    exact ρ₁.property.inter ρ₂.property⟩

/-- `ofSum` acts on the left summand through `ρ₁`. -/
@[simp]
theorem ofSum_val_apply_inl (e : Fin a ⊕ Fin b ≃ Fin n) (ρ₁ : GaloisSet K a) (ρ₂ : GaloisSet K b)
    (σ : Gal(SeparableClosure K/K)) (i : Fin a) :
    (ofSum e ρ₁ ρ₂).val σ (e (.inl i)) = e (.inl (ρ₁.val σ i)) := by
  simp [ofSum]

/-- `ofSum` acts on the right summand through `ρ₂`. -/
@[simp]
theorem ofSum_val_apply_inr (e : Fin a ⊕ Fin b ≃ Fin n) (ρ₁ : GaloisSet K a) (ρ₂ : GaloisSet K b)
    (σ : Gal(SeparableClosure K/K)) (j : Fin b) :
    (ofSum e ρ₁ ρ₂).val σ (e (.inr j)) = e (.inr (ρ₂.val σ j)) := by
  simp [ofSum]

/-- The kernel of `ofSum e ρ₁ ρ₂` is the intersection of the kernels of `ρ₁` and `ρ₂`. -/
@[simp]
theorem ker_ofSum (e : Fin a ⊕ Fin b ≃ Fin n) (ρ₁ : GaloisSet K a) (ρ₂ : GaloisSet K b) :
    (ofSum e ρ₁ ρ₂).val.ker = ρ₁.val.ker ⊓ ρ₂.val.ker := by
  rw [ofSum, MonoidHom.ker_comp_of_injective _ _ e.permCongrHom.injective,
    MonoidHom.ker_comp_of_injective _ _ Equiv.Perm.sumCongrHom_injective, MonoidHom.ker_prod]

/-- `ofSum e` is injective in the pair `(ρ₁, ρ₂)`. -/
@[simp]
theorem ofSum_inj (e : Fin a ⊕ Fin b ≃ Fin n) {ρ₁ τ₁ : GaloisSet K a} {ρ₂ τ₂ : GaloisSet K b} :
    ofSum e ρ₁ ρ₂ = ofSum e τ₁ τ₂ ↔ ρ₁ = τ₁ ∧ ρ₂ = τ₂ := by
  refine ⟨fun h ↦ ⟨ext fun σ i ↦ ?_, ext fun σ j ↦ ?_⟩, fun ⟨h₁, h₂⟩ ↦ h₁ ▸ h₂ ▸ rfl⟩
  · have h' := congrArg (fun ρ : GaloisSet K n ↦ ρ.val σ (e (.inl i))) h
    exact Sum.inl_injective (e.injective (by simpa using h'))
  · have h' := congrArg (fun ρ : GaloisSet K n ↦ ρ.val σ (e (.inr j))) h
    exact Sum.inr_injective (e.injective (by simpa using h'))

/-- Every group element maps the left summand `Set.range (e ∘ Sum.inl)` into itself under
`ofSum e ρ₁ ρ₂`. -/
theorem mapsTo_ofSum_inl (e : Fin a ⊕ Fin b ≃ Fin n) (ρ₁ : GaloisSet K a) (ρ₂ : GaloisSet K b)
    (σ : Gal(SeparableClosure K/K)) :
    Set.MapsTo ((ofSum e ρ₁ ρ₂).val σ) (Set.range (e ∘ Sum.inl)) (Set.range (e ∘ Sum.inl)) := by
  rintro _ ⟨i, rfl⟩
  exact ⟨ρ₁.val σ i, (ofSum_val_apply_inl e ρ₁ ρ₂ σ i).symm⟩

/-- Any labelled Galois set leaving `Set.range (e ∘ Sum.inl)` invariant splits as
`ofSum e ρ₁ ρ₂`. -/
theorem exists_eq_ofSum_of_mapsTo (e : Fin a ⊕ Fin b ≃ Fin n) {ρ : GaloisSet K n}
    (hρ : ∀ σ, Set.MapsTo (ρ.val σ) (Set.range (e ∘ Sum.inl)) (Set.range (e ∘ Sum.inl))) :
    ∃ (ρ₁ : GaloisSet K a) (ρ₂ : GaloisSet K b), ofSum e ρ₁ ρ₂ = ρ := by
  let ψ : Gal(SeparableClosure K/K) →* Equiv.Perm (Fin a ⊕ Fin b) :=
    e.symm.permCongrHom.toMonoidHom.comp ρ.val
  have hψ : ∀ σ, ψ σ ∈ (Equiv.Perm.sumCongrHom (Fin a) (Fin b)).range := by
    intro σ
    refine Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hρ σ ⟨i, rfl⟩
    have hj' : ρ.val σ (e (.inl i)) = e (.inl j) := hj.symm
    exact ⟨j, by simp [ψ, hj']⟩
  let φ : Gal(SeparableClosure K/K) →* Equiv.Perm (Fin a) × Equiv.Perm (Fin b) :=
    (MonoidHom.ofInjective Equiv.Perm.sumCongrHom_injective).symm.toMonoidHom.comp
      (ψ.codRestrict _ hψ)
  let φ₁ := (MonoidHom.fst (Equiv.Perm (Fin a)) (Equiv.Perm (Fin b))).comp φ
  let φ₂ := (MonoidHom.snd (Equiv.Perm (Fin a)) (Equiv.Perm (Fin b))).comp φ
  have hsum : (Equiv.Perm.sumCongrHom (Fin a) (Fin b)).comp (φ₁.prod φ₂) = ψ := by
    ext σ x
    simp [φ₁, φ₂, φ]
  have hker : ρ.val.ker ≤ φ₁.ker ⊓ φ₂.ker := by
    have : ψ.ker = (φ₁.prod φ₂).ker := by
      rw [← hsum, MonoidHom.ker_comp_of_injective _ _ Equiv.Perm.sumCongrHom_injective]
    rw [← MonoidHom.ker_prod, ← this]
    exact le_of_eq (MonoidHom.ker_comp_of_injective _ _ e.symm.permCongrHom.injective).symm
  refine ⟨⟨φ₁, Subgroup.isOpen_mono (hker.trans inf_le_left) ρ.property⟩,
    ⟨φ₂, Subgroup.isOpen_mono (hker.trans inf_le_right) ρ.property⟩, ext fun σ x ↦ ?_⟩
  have hx := congrArg (fun p : Equiv.Perm (Fin a ⊕ Fin b) ↦ e (p (e.symm x)))
    (congrArg (fun f : Gal(SeparableClosure K/K) →* Equiv.Perm (Fin a ⊕ Fin b) ↦ f σ) hsum)
  simpa [ofSum, ψ] using hx

/-- `ofSum e` identifies pairs of labelled Galois sets with the labelled Galois sets on `Fin n`
leaving `Set.range (e ∘ Sum.inl)` invariant. -/
def ofSumEquiv (e : Fin a ⊕ Fin b ≃ Fin n) :
    GaloisSet K a × GaloisSet K b ≃
      {ρ : GaloisSet K n //
        ∀ σ, Set.MapsTo (ρ.val σ) (Set.range (e ∘ Sum.inl)) (Set.range (e ∘ Sum.inl))} :=
  Equiv.ofBijective (fun p ↦ ⟨ofSum e p.1 p.2, mapsTo_ofSum_inl e p.1 p.2⟩)
    ⟨fun _ _ h ↦ Prod.ext_iff.2 ((ofSum_inj e).1 (congrArg Subtype.val h)),
      fun ⟨_, hρ⟩ ↦ let ⟨ρ₁, ρ₂, h⟩ := exists_eq_ofSum_of_mapsTo e hρ; ⟨(ρ₁, ρ₂), Subtype.ext h⟩⟩

/-- `ofSumEquiv e` evaluates to `ofSum e` on the pair. -/
@[simp]
theorem coe_ofSumEquiv_apply (e : Fin a ⊕ Fin b ≃ Fin n) (p : GaloisSet K a × GaloisSet K b) :
    (ofSumEquiv (K := K) e p : GaloisSet K n) = ofSum e p.1 p.2 :=
  (rfl)

/-- The inverse of `ofSumEquiv e` recovers `(ρ₁, ρ₂)` from `ofSum e ρ₁ ρ₂`. -/
@[simp]
theorem ofSumEquiv_symm_apply (e : Fin a ⊕ Fin b ≃ Fin n) (ρ₁ : GaloisSet K a)
    (ρ₂ : GaloisSet K b)
    (h : ∀ σ, Set.MapsTo ((ofSum e ρ₁ ρ₂).val σ)
      (Set.range (e ∘ Sum.inl)) (Set.range (e ∘ Sum.inl))) :
    (ofSumEquiv e).symm ⟨ofSum e ρ₁ ρ₂, h⟩ = (ρ₁, ρ₂) :=
  (ofSumEquiv e).symm_apply_eq.2 (Subtype.ext rfl)

/-- For a point `i : Fin a` in the left summand, its orbit in `ofSum e ρ₁ ρ₂` fills the entire left
summand `Set.range (e ∘ Sum.inl)` precisely when `ρ₁` is transitive. -/
theorem orbit_ofSum_inl_eq_range_iff (e : Fin a ⊕ Fin b ≃ Fin n) (ρ₁ : GaloisSet K a)
    (ρ₂ : GaloisSet K b) (i : Fin a) :
    (letI := (ofSum e ρ₁ ρ₂).mulAction;
      MulAction.orbit Gal(SeparableClosure K/K) (e (.inl i))) = Set.range (e ∘ Sum.inl) ↔
      ρ₁.IsTransitive := by
  let := (ofSum e ρ₁ ρ₂).mulAction
  constructor
  · intro horb
    rw [isTransitive_iff]
    have hi : ∀ j : Fin a, ∃ σ : Gal(SeparableClosure K/K), ρ₁.val σ i = j := by
      intro j
      have hj : e (.inl j) ∈ MulAction.orbit Gal(SeparableClosure K/K) (e (.inl i)) :=
        horb ▸ ⟨j, rfl⟩
      obtain ⟨σ, hσ⟩ := hj
      exact ⟨σ, Sum.inl_injective (e.injective (by simpa using hσ))⟩
    intro j₁ j₂
    obtain ⟨σ₁, rfl⟩ := hi j₁
    obtain ⟨σ₂, rfl⟩ := hi j₂
    exact ⟨σ₂ * σ₁⁻¹, by simp⟩
  · intro hρ₁
    ext x
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨ρ₁.val σ i, (ofSum_val_apply_inl e ρ₁ ρ₂ σ i).symm⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨σ, rfl⟩ := ρ₁.isTransitive_iff.1 hρ₁ i j
      exact ⟨σ, ofSum_val_apply_inl e ρ₁ ρ₂ σ i⟩

end ofSum

section OrbitDecomposition

variable {n : ℕ}

open scoped Classical in
/-- The orbit of a label `i : Fin n` under a labelled Galois set `ρ`, as a `Finset (Fin n)`. -/
def orbitFinset (ρ : GaloisSet K n) (i : Fin n) : Finset (Fin n) :=
  letI := ρ.mulAction
  (MulAction.orbit Gal(SeparableClosure K/K) i).toFinset

/-- A label `j` lies in `ρ.orbitFinset i` precisely when some group element sends `i` to `j`. -/
@[grind =]
theorem mem_orbitFinset_iff (ρ : GaloisSet K n) (i j : Fin n) :
    j ∈ ρ.orbitFinset i ↔ ∃ σ : Gal(SeparableClosure K/K), ρ.val σ i = j := by
  let := ρ.mulAction
  simp [orbitFinset, MulAction.mem_orbit_iff]

/-- As a set, `ρ.orbitFinset i` is the orbit of `i`. -/
@[simp]
theorem coe_orbitFinset (ρ : GaloisSet K n) (i : Fin n) :
    (ρ.orbitFinset i : Set (Fin n)) =
      (letI := ρ.mulAction; MulAction.orbit Gal(SeparableClosure K/K) i) := by
  ext j
  simp [mem_orbitFinset_iff, MulAction.mem_orbit_iff]

/-- Every label lies in its own orbit finset. -/
@[simp]
theorem mem_orbitFinset_self (ρ : GaloisSet K n) (i : Fin n) : i ∈ ρ.orbitFinset i :=
  (ρ.mem_orbitFinset_iff i i).2 ⟨1, by simp⟩

/-- Every group element sends `i` into `ρ.orbitFinset i`. -/
@[simp]
theorem val_apply_mem_orbitFinset (ρ : GaloisSet K n) (σ : Gal(SeparableClosure K/K))
    (i : Fin n) : ρ.val σ i ∈ ρ.orbitFinset i :=
  (ρ.mem_orbitFinset_iff i _).2 ⟨σ, rfl⟩

/-- In the trivial Galois set, the orbit finset of every label is a singleton. -/
@[simp]
theorem orbitFinset_trivial (i : Fin n) : (trivial K n).orbitFinset i = {i} := by
  ext j
  simp [mem_orbitFinset_iff, eq_comm]

/-- In `ofSum e ρ₁ ρ₂`, the orbit finset of a left-summand label `e (.inl i)` is the embedded
orbit finset of `i` in `ρ₁`. -/
@[simp]
theorem orbitFinset_ofSum_inl {a b : ℕ} (e : Fin a ⊕ Fin b ≃ Fin n) (ρ₁ : GaloisSet K a)
    (ρ₂ : GaloisSet K b) (i : Fin a) :
    (ofSum e ρ₁ ρ₂).orbitFinset (e (.inl i)) =
      (ρ₁.orbitFinset i).map (Function.Embedding.inl.trans e.toEmbedding) := by
  ext x
  simp only [mem_orbitFinset_iff, Finset.mem_map, Function.Embedding.trans_apply,
    Function.Embedding.inl_apply, Equiv.coe_toEmbedding]
  exact ⟨fun ⟨σ, hσ⟩ ↦ ⟨ρ₁.val σ i, ⟨σ, rfl⟩, (ofSum_val_apply_inl e ρ₁ ρ₂ σ i).symm.trans hσ⟩,
    fun ⟨_, ⟨σ, hj⟩, hx⟩ ↦ ⟨σ, (ofSum_val_apply_inl e ρ₁ ρ₂ σ i).trans
      ((congrArg (fun y ↦ e (.inl y)) hj).trans hx)⟩⟩

/-- In `ofSum e ρ₁ ρ₂`, the orbit finset of a right-summand label `e (.inr j)` is the embedded
orbit finset of `j` in `ρ₂`. -/
@[simp]
theorem orbitFinset_ofSum_inr {a b : ℕ} (e : Fin a ⊕ Fin b ≃ Fin n) (ρ₁ : GaloisSet K a)
    (ρ₂ : GaloisSet K b) (j : Fin b) :
    (ofSum e ρ₁ ρ₂).orbitFinset (e (.inr j)) =
      (ρ₂.orbitFinset j).map (Function.Embedding.inr.trans e.toEmbedding) := by
  ext x
  simp only [mem_orbitFinset_iff, Finset.mem_map, Function.Embedding.trans_apply,
    Function.Embedding.inr_apply, Equiv.coe_toEmbedding]
  exact ⟨fun ⟨σ, hσ⟩ ↦ ⟨ρ₂.val σ j, ⟨σ, rfl⟩, (ofSum_val_apply_inr e ρ₁ ρ₂ σ j).symm.trans hσ⟩,
    fun ⟨_, ⟨σ, hk⟩, hx⟩ ↦ ⟨σ, (ofSum_val_apply_inr e ρ₁ ρ₂ σ j).trans
      ((congrArg (fun y ↦ e (.inr y)) hk).trans hx)⟩⟩

/-- The orbit finset of any label is nonempty, hence has positive cardinality. -/
theorem card_orbitFinset_pos (ρ : GaloisSet K n) (i : Fin n) : 0 < (ρ.orbitFinset i).card :=
  Finset.card_pos.2 ⟨i, ρ.mem_orbitFinset_self i⟩

/-- The orbit finset has cardinality at most `n`. -/
theorem card_orbitFinset_le (ρ : GaloisSet K n) (i : Fin n) : (ρ.orbitFinset i).card ≤ n :=
  (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)

/-- Every group element maps `ρ.orbitFinset i` into itself. -/
theorem mapsTo_orbitFinset (ρ : GaloisSet K n) (i : Fin n) (σ : Gal(SeparableClosure K/K)) :
    Set.MapsTo (ρ.val σ) (ρ.orbitFinset i : Set (Fin n)) (ρ.orbitFinset i : Set (Fin n)) := by
  intro j hj
  obtain ⟨τ, rfl⟩ := (ρ.mem_orbitFinset_iff i j).1 hj
  exact (ρ.mem_orbitFinset_iff i _).2 ⟨σ * τ, by simp⟩

/-- For `i₀ ∈ S`, the orbit of `i₀` in `ofSum (finSumEquivOfFinset hm hk) ρ₁ ρ₂` is `S` precisely
when `ρ₁` is transitive. -/
@[simp]
theorem orbitFinset_ofSum_finSumEquivOfFinset_eq_iff {S : Finset (Fin n)} {m k : ℕ}
    (hm : S.card = m) (hk : Sᶜ.card = k) {i₀ : Fin n} (hi₀ : i₀ ∈ S)
    (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K k) :
    (ofSum (finSumEquivOfFinset hm hk) ρ₁ ρ₂).orbitFinset i₀ = S ↔ ρ₁.IsTransitive := by
  let j₀ : Fin m := (S.orderIsoOfFin hm).symm ⟨i₀, hi₀⟩
  have hj₀ : finSumEquivOfFinset hm hk (.inl j₀) = i₀ := by
    simp [j₀, ← Finset.coe_orderIsoOfFin_apply]
  have hrange : Set.range (finSumEquivOfFinset hm hk ∘ Sum.inl) = (S : Set (Fin n)) := by
    simp [Function.comp_def]
  rw [← Finset.coe_inj, coe_orbitFinset, ← hj₀, ← hrange, orbit_ofSum_inl_eq_range_iff]

/-- **Orbit decomposition at a chosen point**: every labelled Galois set of size `n` is uniquely
determined by the size `m ∈ [1, n]` of the orbit of `i₀`, the `m`-element subset `S ⊆ Fin n`
containing `i₀` that forms that orbit, a transitive Galois set on `Fin m`, and a Galois set on the
remaining `n - m` points. -/
def orbitDecompositionEquiv (i₀ : Fin n) :
    GaloisSet K n ≃
      Σ m : Finset.Icc 1 n,
        ((Finset.univ.powersetCard m.1).filter (i₀ ∈ ·)) ×
          {ρ₁ : GaloisSet K m.1 // ρ₁.IsTransitive} ×
          GaloisSet K (n - m.1) :=
  (Equiv.ofBijective
    (fun q : (Σ m : Finset.Icc 1 n,
        ((Finset.univ.powersetCard m.1).filter (i₀ ∈ ·)) ×
          {ρ₁ : GaloisSet K m.1 // ρ₁.IsTransitive} ×
          GaloisSet K (n - m.1)) ↦
      have hm : q.2.1.1.card = q.1.1 :=
        (Finset.mem_powersetCard.1 (Finset.mem_filter.1 q.2.1.2).1).2
      ofSum (finSumEquivOfFinset hm (by rw [Finset.card_compl, Fintype.card_fin, hm]))
        q.2.2.1.1 q.2.2.2)
    ⟨by
      -- Injectivity: the orbit of `i₀` recovers `S` and `m`, then `ofSum_inj` recovers `(ρ₁, ρ₂)`.
      rintro ⟨m, S, ρ₁, ρ₂⟩ ⟨m', S', ρ₁', ρ₂'⟩ h
      have hS : S.1 = S'.1 := by
        have horb := congrArg (fun ρ : GaloisSet K n ↦ ρ.orbitFinset i₀) h
        rwa [(orbitFinset_ofSum_finSumEquivOfFinset_eq_iff _ _
              (Finset.mem_filter.1 S.2).2 _ _).2 ρ₁.2,
            (orbitFinset_ofSum_finSumEquivOfFinset_eq_iff _ _
              (Finset.mem_filter.1 S'.2).2 _ _).2 ρ₁'.2] at horb
      have hm : m = m' := Subtype.ext <|
        (Finset.mem_powersetCard.1 (Finset.mem_filter.1 S.2).1).2.symm.trans
          (hS ▸ (Finset.mem_powersetCard.1 (Finset.mem_filter.1 S'.2).1).2)
      subst hm
      have hSS : S = S' := Subtype.ext hS
      subst hSS
      obtain ⟨h₁, h₂⟩ := (ofSum_inj _).1 h
      exact congrArg (Sigma.mk m) (Prod.ext rfl (Prod.ext (Subtype.ext h₁) h₂)),
    by
      -- Surjectivity: split `ρ` along the orbit `S = ρ.orbitFinset i₀`.
      intro ρ
      let S := ρ.orbitFinset i₀
      have hm : S.card ∈ Finset.Icc 1 n :=
        Finset.mem_Icc.2 ⟨ρ.card_orbitFinset_pos i₀, ρ.card_orbitFinset_le i₀⟩
      have hS : S ∈ (Finset.univ.powersetCard S.card).filter (i₀ ∈ ·) :=
        Finset.mem_filter.2 ⟨Finset.mem_powersetCard.2 ⟨Finset.subset_univ S, rfl⟩,
          ρ.mem_orbitFinset_self i₀⟩
      have hk : Sᶜ.card = n - S.card := by rw [Finset.card_compl, Fintype.card_fin]
      have hmaps : ∀ σ, Set.MapsTo (ρ.val σ)
          (Set.range (finSumEquivOfFinset (s := S) rfl hk ∘ Sum.inl))
          (Set.range (finSumEquivOfFinset (s := S) rfl hk ∘ Sum.inl)) := by
        have hrange : Set.range (finSumEquivOfFinset (s := S) rfl hk ∘ Sum.inl) =
            (S : Set (Fin n)) := by simp [Function.comp_def]
        rw [hrange]
        exact ρ.mapsTo_orbitFinset i₀
      obtain ⟨ρ₁, ρ₂, hρ⟩ := exists_eq_ofSum_of_mapsTo (finSumEquivOfFinset rfl hk) hmaps
      have htrans : ρ₁.IsTransitive :=
        (orbitFinset_ofSum_finSumEquivOfFinset_eq_iff rfl hk (ρ.mem_orbitFinset_self i₀)
          ρ₁ ρ₂).1 (hρ.symm ▸ rfl)
      exact ⟨⟨⟨S.card, hm⟩, ⟨S, hS⟩, ⟨ρ₁, htrans⟩, ρ₂⟩, hρ⟩⟩).symm

/-- The inverse of `orbitDecompositionEquiv i₀` glues `ρ₁` and `ρ₂` along `finSumEquivOfFinset` for
the chosen subset `S`. -/
@[simp]
theorem orbitDecompositionEquiv_symm_apply (i₀ : Fin n)
    (m : Finset.Icc 1 n) (S : (Finset.univ.powersetCard m.1).filter (i₀ ∈ ·))
    (ρ₁ : {ρ₁ : GaloisSet K m.1 // ρ₁.IsTransitive}) (ρ₂ : GaloisSet K (n - m.1)) :
    (orbitDecompositionEquiv (K := K) i₀).symm ⟨m, S, ρ₁, ρ₂⟩ =
      (have hm : S.1.card = m.1 := (Finset.mem_powersetCard.1 (Finset.mem_filter.1 S.2).1).2
      ofSum (finSumEquivOfFinset hm (by rw [Finset.card_compl, Fintype.card_fin, hm])) ρ₁.1 ρ₂) :=
  (rfl)

/-- The subset component of `orbitDecompositionEquiv i₀ ρ` is the orbit finset of `i₀`. -/
@[simp]
theorem coe_orbitDecompositionEquiv_apply_snd_fst (i₀ : Fin n) (ρ : GaloisSet K n) :
    ((orbitDecompositionEquiv i₀ ρ).2.1 : Finset (Fin n)) = ρ.orbitFinset i₀ := by
  set q := orbitDecompositionEquiv i₀ ρ
  have hsymm : (orbitDecompositionEquiv i₀).symm q = ρ :=
    (orbitDecompositionEquiv i₀).symm_apply_apply ρ
  have horb := congrArg (·.orbitFinset i₀) hsymm
  rw [orbitDecompositionEquiv_symm_apply,
    (orbitFinset_ofSum_finSumEquivOfFinset_eq_iff _ _
      (Finset.mem_filter.1 q.2.1.2).2 _ _).2 q.2.2.1.2] at horb
  exact horb

/-- The size component of `orbitDecompositionEquiv i₀ ρ` is the cardinality of the orbit finset of
`i₀`. -/
@[simp]
theorem coe_orbitDecompositionEquiv_apply_fst (i₀ : Fin n) (ρ : GaloisSet K n) :
    ((orbitDecompositionEquiv i₀ ρ).1 : ℕ) = (ρ.orbitFinset i₀).card := by
  rw [← coe_orbitDecompositionEquiv_apply_snd_fst i₀ ρ]
  exact (Finset.mem_powersetCard.1
    (Finset.mem_filter.1 (orbitDecompositionEquiv i₀ ρ).2.1.2).1).2.symm

end OrbitDecomposition

end TauCeti.GaloisSet
