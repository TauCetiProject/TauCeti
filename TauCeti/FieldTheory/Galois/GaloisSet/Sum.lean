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
import TauCeti.Algebra.GroupAction.OrbitRelQuotient

/-!
# Disjoint unions and orbit decompositions of labelled Galois sets

Two labelled Galois sets `ρ₁ : GaloisSet K m` and `ρ₂ : GaloisSet K k` combine along any bijection
`e : Fin m ⊕ Fin k ≃ Fin n` into a labelled Galois set `GaloisSet.sumCongr e ρ₁ ρ₂` of size `n`.
Its Galois action preserves the image of `Fin m` and restricts to `ρ₁` and `ρ₂` on the two
summands; conversely every labelled Galois set preserving `Set.range (e ∘ Sum.inl)` arises from a
unique pair `(ρ₁, ρ₂)` (`GaloisSet.sumCongrEquiv`).

Specialising `e` to `finSumEquivOfFinset` for a subset `s` of `Fin n` containing a chosen base
label `i₀` decomposes the labelled Galois sets in which the orbit of `i₀` has cardinality `m` into
the `m`-element subsets containing `i₀`, a transitive Galois set on `Fin m`, and an arbitrary
Galois set on `Fin (n - m)` (`GaloisSet.orbitCardEquiv`). Peeling off one orbit at a time in this
way reduces sums over all Galois sets with a prescribed orbit structure to sums over transitive
Galois sets.

## Main definitions and results

* `TauCeti.GaloisSet.sumCongr`: transport the disjoint union of two labelled Galois sets along an
  equivalence `Fin m ⊕ Fin k ≃ Fin n`.
* `TauCeti.GaloisSet.sumCongrEquiv`: equivalence with the labelled Galois sets leaving
  `Set.range (e ∘ Sum.inl)` invariant.
* `TauCeti.GaloisSet.orbit_sumCongr_inl_eq_range_iff`: the orbit of a left label is the entire
  left summand precisely when the left Galois set is transitive.
* `TauCeti.GaloisSet.orbitCardEquiv`: equivalence between labelled Galois sets whose orbit of `i₀`
  has size `m` and triples of an `m`-subset containing `i₀`, a transitive Galois set of size `m`,
  and a Galois set of size `n - m`.
-/

public section

noncomputable section

namespace TauCeti.GaloisSet

universe u

variable {K : Type u} [Field K] {m k n : ℕ}

/-- Combine two labelled Galois sets of sizes `m` and `k` into one of size `n` along a bijection
`e : Fin m ⊕ Fin k ≃ Fin n`. Its kernel is the intersection of the two kernels, hence open. -/
def sumCongr (e : Fin m ⊕ Fin k ≃ Fin n) (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K k) :
    GaloisSet K n :=
  ⟨(e.permCongrHom.toMonoidHom.comp (Equiv.Perm.sumCongrHom (Fin m) (Fin k))).comp
      (ρ₁.val.prod ρ₂.val), by
    rw [MonoidHom.ker_comp_of_injective _ _
      (e.permCongrHom.injective.comp Equiv.Perm.sumCongrHom_injective), MonoidHom.ker_prod]
    exact ρ₁.property.inter ρ₂.property⟩

/-- `sumCongr e ρ₁ ρ₂` acts on `Fin n` by transporting `Equiv.sumCongr (ρ₁ σ) (ρ₂ σ)` along `e`. -/
@[simp]
theorem sumCongr_val_apply (e : Fin m ⊕ Fin k ≃ Fin n) (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K k)
    (σ : Gal(SeparableClosure K/K)) (i : Fin n) :
    (sumCongr e ρ₁ ρ₂).val σ i = e (Equiv.sumCongr (ρ₁.val σ) (ρ₂.val σ) (e.symm i)) :=
  (rfl)

/-- On the image of the left summand, `sumCongr e ρ₁ ρ₂` acts through `ρ₁`. -/
theorem sumCongr_val_apply_inl (e : Fin m ⊕ Fin k ≃ Fin n) (ρ₁ : GaloisSet K m)
    (ρ₂ : GaloisSet K k) (σ : Gal(SeparableClosure K/K)) (i : Fin m) :
    (sumCongr e ρ₁ ρ₂).val σ (e (Sum.inl i)) = e (Sum.inl (ρ₁.val σ i)) := by
  simp

/-- On the image of the right summand, `sumCongr e ρ₁ ρ₂` acts through `ρ₂`. -/
theorem sumCongr_val_apply_inr (e : Fin m ⊕ Fin k ≃ Fin n) (ρ₁ : GaloisSet K m)
    (ρ₂ : GaloisSet K k) (σ : Gal(SeparableClosure K/K)) (j : Fin k) :
    (sumCongr e ρ₁ ρ₂).val σ (e (Sum.inr j)) = e (Sum.inr (ρ₂.val σ j)) := by
  simp

/-- Combining two labelled Galois sets along a bijection `e` is injective in the pair `(ρ₁, ρ₂)`. -/
theorem sumCongr_injective (e : Fin m ⊕ Fin k ≃ Fin n) :
    Function.Injective (Function.uncurry (sumCongr (K := K) e)) := by
  rintro ⟨ρ₁, ρ₂⟩ ⟨τ₁, τ₂⟩ h
  refine Prod.ext (ext fun σ i ↦ ?_) (ext fun σ j ↦ ?_)
  · have h' := congrArg (fun ρ : GaloisSet K n ↦ ρ.val σ (e (Sum.inl i))) h
    exact Sum.inl_injective (e.injective (by simpa using h'))
  · have h' := congrArg (fun ρ : GaloisSet K n ↦ ρ.val σ (e (Sum.inr j))) h
    exact Sum.inr_injective (e.injective (by simpa using h'))

/-- Equality of `sumCongr e` combinations is equality of both summands. -/
@[simp]
theorem sumCongr_inj (e : Fin m ⊕ Fin k ≃ Fin n) {ρ₁ τ₁ : GaloisSet K m} {ρ₂ τ₂ : GaloisSet K k} :
    sumCongr e ρ₁ ρ₂ = sumCongr e τ₁ τ₂ ↔ ρ₁ = τ₁ ∧ ρ₂ = τ₂ :=
  ⟨fun h ↦ Prod.ext_iff.1 (sumCongr_injective e (a₁ := (ρ₁, ρ₂)) (a₂ := (τ₁, τ₂)) h),
    fun ⟨h₁, h₂⟩ ↦ h₁ ▸ h₂ ▸ rfl⟩

/-- A left label `e (Sum.inl i)` has the same point stabilizer in `sumCongr e ρ₁ ρ₂` as `i` in
`ρ₁`. -/
theorem stabilizer_sumCongr_inl (e : Fin m ⊕ Fin k ≃ Fin n) (ρ₁ : GaloisSet K m)
    (ρ₂ : GaloisSet K k) (i : Fin m) :
    (letI := (sumCongr e ρ₁ ρ₂).mulAction
    MulAction.stabilizer Gal(SeparableClosure K/K) (e (Sum.inl i))) =
      (letI := ρ₁.mulAction
      MulAction.stabilizer Gal(SeparableClosure K/K) i) := by
  let := (sumCongr e ρ₁ ρ₂).mulAction
  let := ρ₁.mulAction
  exact MulAction.stabilizer_eq_of_injective (e ∘ Sum.inl)
    (e.injective.comp Sum.inl_injective) (fun σ j ↦ (sumCongr_val_apply_inl e ρ₁ ρ₂ σ j).symm) i

/-- A right label `e (Sum.inr j)` has the same point stabilizer in `sumCongr e ρ₁ ρ₂` as `j` in
`ρ₂`. -/
theorem stabilizer_sumCongr_inr (e : Fin m ⊕ Fin k ≃ Fin n) (ρ₁ : GaloisSet K m)
    (ρ₂ : GaloisSet K k) (j : Fin k) :
    (letI := (sumCongr e ρ₁ ρ₂).mulAction
    MulAction.stabilizer Gal(SeparableClosure K/K) (e (Sum.inr j))) =
      (letI := ρ₂.mulAction
      MulAction.stabilizer Gal(SeparableClosure K/K) j) := by
  let := (sumCongr e ρ₁ ρ₂).mulAction
  let := ρ₂.mulAction
  exact MulAction.stabilizer_eq_of_injective (e ∘ Sum.inr)
    (e.injective.comp Sum.inr_injective) (fun σ j' ↦ (sumCongr_val_apply_inr e ρ₁ ρ₂ σ j').symm) j

/-- The orbit space of `sumCongr e ρ₁ ρ₂` is the disjoint union of the orbit spaces of `ρ₁` and
`ρ₂`. -/
def orbitRelQuotientSumCongr (e : Fin m ⊕ Fin k ≃ Fin n) (ρ₁ : GaloisSet K m)
    (ρ₂ : GaloisSet K k) :
    (letI := ρ₁.mulAction
    MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin m)) ⊕
      (letI := ρ₂.mulAction
      MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin k)) ≃
    (letI := (sumCongr e ρ₁ ρ₂).mulAction
    MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) :=
  letI := ρ₁.mulAction
  letI := ρ₂.mulAction
  letI := (sumCongr e ρ₁ ρ₂).mulAction
  MulAction.orbitRelQuotientSumEquiv.symm.trans
    (MulAction.orbitRelQuotientCongr (MulEquiv.refl Gal(SeparableClosure K/K)) e fun σ x ↦
      match x with
      | Sum.inl i => (sumCongr_val_apply_inl e ρ₁ ρ₂ σ i).symm
      | Sum.inr j => (sumCongr_val_apply_inr e ρ₁ ρ₂ σ j).symm)

/-- `orbitRelQuotientSumCongr` maps a left orbit `⟦i⟧` to `⟦e (Sum.inl i)⟧`. -/
@[simp]
theorem orbitRelQuotientSumCongr_inl_mk (e : Fin m ⊕ Fin k ≃ Fin n) (ρ₁ : GaloisSet K m)
    (ρ₂ : GaloisSet K k) (i : Fin m) :
    orbitRelQuotientSumCongr e ρ₁ ρ₂
      (Sum.inl (letI := ρ₁.mulAction; Quotient.mk'' i)) =
      (letI := (sumCongr e ρ₁ ρ₂).mulAction; Quotient.mk'' (e (Sum.inl i))) := by
  let := ρ₁.mulAction
  let := ρ₂.mulAction
  let := (sumCongr e ρ₁ ρ₂).mulAction
  simp [orbitRelQuotientSumCongr]

/-- `orbitRelQuotientSumCongr` maps a right orbit `⟦j⟧` to `⟦e (Sum.inr j)⟧`. -/
@[simp]
theorem orbitRelQuotientSumCongr_inr_mk (e : Fin m ⊕ Fin k ≃ Fin n) (ρ₁ : GaloisSet K m)
    (ρ₂ : GaloisSet K k) (j : Fin k) :
    orbitRelQuotientSumCongr e ρ₁ ρ₂
      (Sum.inr (letI := ρ₂.mulAction; Quotient.mk'' j)) =
      (letI := (sumCongr e ρ₁ ρ₂).mulAction; Quotient.mk'' (e (Sum.inr j))) := by
  let := ρ₁.mulAction
  let := ρ₂.mulAction
  let := (sumCongr e ρ₁ ρ₂).mulAction
  simp [orbitRelQuotientSumCongr]

/-- The orbit of `e (Sum.inl i)` in `sumCongr e ρ₁ ρ₂` is the image under `e ∘ Sum.inl` of the
orbit of `i` in `ρ₁`. -/
theorem orbit_sumCongr_inl (e : Fin m ⊕ Fin k ≃ Fin n) (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K k)
    (i : Fin m) :
    (letI := (sumCongr e ρ₁ ρ₂).mulAction
    MulAction.orbit Gal(SeparableClosure K/K) (e (Sum.inl i))) =
      (letI := ρ₁.mulAction
      (e ∘ Sum.inl) '' MulAction.orbit Gal(SeparableClosure K/K) i) := by
  let := (sumCongr e ρ₁ ρ₂).mulAction
  let := ρ₁.mulAction
  ext x
  simp only [MulAction.mem_orbit_iff, smul_def, Set.mem_image, Function.comp_apply]
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨ρ₁.val σ i, ⟨σ, rfl⟩, (sumCongr_val_apply_inl e ρ₁ ρ₂ σ i).symm⟩
  · rintro ⟨j, ⟨σ, rfl⟩, rfl⟩
    exact ⟨σ, sumCongr_val_apply_inl e ρ₁ ρ₂ σ i⟩

/-- For a label `i : Fin m`, the orbit of `e (Sum.inl i)` in `sumCongr e ρ₁ ρ₂` is the entire
left block `Set.range (e ∘ Sum.inl)` precisely when `ρ₁` is transitive. -/
theorem orbit_sumCongr_inl_eq_range_iff (e : Fin m ⊕ Fin k ≃ Fin n) (ρ₁ : GaloisSet K m)
    (ρ₂ : GaloisSet K k) (i : Fin m) :
    (letI := (sumCongr e ρ₁ ρ₂).mulAction
    MulAction.orbit Gal(SeparableClosure K/K) (e (Sum.inl i)) =
      Set.range (e ∘ Sum.inl)) ↔ ρ₁.IsTransitive := by
  let := (sumCongr e ρ₁ ρ₂).mulAction
  let := ρ₁.mulAction
  rw [orbit_sumCongr_inl, ← Set.image_univ,
    Set.image_eq_image (e.injective.comp Sum.inl_injective), isTransitive_def,
    MulAction.isPretransitive_iff_orbit_eq_univ i]

/-- **Splitting a Galois set along an invariant summand.** Pairs `(ρ₁, ρ₂)` correspond along
`sumCongr e` to the labelled Galois sets of size `n` that map `Set.range (e ∘ Sum.inl)` into
itself. -/
def sumCongrEquiv (e : Fin m ⊕ Fin k ≃ Fin n) :
    GaloisSet K m × GaloisSet K k ≃
      {ρ : GaloisSet K n // ∀ (σ : Gal(SeparableClosure K/K)) (i : Fin m),
        ρ.val σ (e (Sum.inl i)) ∈ Set.range (e ∘ Sum.inl)} :=
  Equiv.ofBijective
    (fun p ↦ ⟨sumCongr e p.1 p.2, fun σ i ↦ ⟨p.1.val σ i, by simp⟩⟩)
    ⟨fun p q h ↦ sumCongr_injective e (congrArg Subtype.val h), fun ⟨ρ, hρ⟩ ↦ by
      -- Pull `ρ` back to `Perm (Fin m ⊕ Fin k)` and factor through `sumCongrHom`.
      let φ : Gal(SeparableClosure K/K) →* Equiv.Perm (Fin m ⊕ Fin k) :=
        e.symm.permCongrHom.toMonoidHom.comp ρ.val
      have hmem : ∀ σ, φ σ ∈ (Equiv.Perm.sumCongrHom (Fin m) (Fin k)).range := by
        intro σ
        refine Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl ?_
        rintro _ ⟨i, rfl⟩
        obtain ⟨i', hi'⟩ := hρ σ i
        exact ⟨i', by simp [φ, ← hi']⟩
      let ψ : Gal(SeparableClosure K/K) →* Equiv.Perm (Fin m) × Equiv.Perm (Fin k) :=
        (MonoidHom.ofInjective Equiv.Perm.sumCongrHom_injective).symm.toMonoidHom.comp
          (φ.codRestrict _ hmem)
      have hψ : (e.permCongrHom.toMonoidHom.comp (Equiv.Perm.sumCongrHom (Fin m) (Fin k))).comp ψ =
          ρ.val := by
        refine MonoidHom.ext fun σ ↦ Equiv.Perm.ext fun j ↦ ?_
        have h1 : Equiv.Perm.sumCongrHom (Fin m) (Fin k) (ψ σ) = φ σ :=
          congrArg Subtype.val
            ((MonoidHom.ofInjective Equiv.Perm.sumCongrHom_injective).apply_symm_apply
              ⟨φ σ, hmem σ⟩)
        simpa [φ] using congrArg (fun p : Equiv.Perm (Fin m ⊕ Fin k) ↦ e (p (e.symm j))) h1
      have hker : IsOpen (ψ.ker : Set Gal(SeparableClosure K/K)) := by
        have hk : ψ.ker = ρ.val.ker := by
          rw [← hψ]
          exact (MonoidHom.ker_comp_of_injective ψ
            (e.permCongrHom.toMonoidHom.comp (Equiv.Perm.sumCongrHom (Fin m) (Fin k)))
            (e.permCongrHom.injective.comp Equiv.Perm.sumCongrHom_injective)).symm
        exact hk ▸ ρ.property
      let ρ₁ : GaloisSet K m := ⟨(MonoidHom.fst _ _).comp ψ,
        Subgroup.isOpen_mono (fun σ hσ ↦ by
          rw [MonoidHom.mem_ker] at hσ ⊢
          simp [hσ]) hker⟩
      let ρ₂ : GaloisSet K k := ⟨(MonoidHom.snd _ _).comp ψ,
        Subgroup.isOpen_mono (fun σ hσ ↦ by
          rw [MonoidHom.mem_ker] at hσ ⊢
          simp [hσ]) hker⟩
      refine ⟨(ρ₁, ρ₂), Subtype.ext (Subtype.ext ?_)⟩
      have hprod : ρ₁.val.prod ρ₂.val = ψ := by ext σ <;> rfl
      exact (congrArg ((e.permCongrHom.toMonoidHom.comp
        (Equiv.Perm.sumCongrHom (Fin m) (Fin k))).comp ·) hprod).trans hψ⟩

/-- `sumCongrEquiv e` sends `(ρ₁, ρ₂)` to `sumCongr e ρ₁ ρ₂`. -/
@[simp]
theorem coe_sumCongrEquiv_apply (e : Fin m ⊕ Fin k ≃ Fin n)
    (p : GaloisSet K m × GaloisSet K k) :
    (sumCongrEquiv e p : GaloisSet K n) = sumCongr e p.1 p.2 :=
  (rfl)

section OrbitCard

private abbrev finSumEquivOfCard {s : Finset (Fin n)} (hs : s.card = m) :
    Fin m ⊕ Fin (n - m) ≃ Fin n :=
  finSumEquivOfFinset hs (by rw [Finset.card_compl, Fintype.card_fin, hs])

private theorem range_finSumEquivOfCard_inl {s : Finset (Fin n)} (hs : s.card = m) :
    Set.range (finSumEquivOfCard hs ∘ Sum.inl) = (s : Set (Fin n)) := by
  have : finSumEquivOfCard hs ∘ Sum.inl = s.orderEmbOfFin hs := by
    ext i
    simp [finSumEquivOfCard]
  rw [this, Finset.range_orderEmbOfFin]

private theorem orbit_sumCongr_finSumEquivOfCard {s : Finset (Fin n)} (hs : s.card = m)
    {i₀ : Fin n} (hi₀ : i₀ ∈ s) (ρ₁ : GaloisSet K m) (hρ₁ : ρ₁.IsTransitive)
    (ρ₂ : GaloisSet K (n - m)) :
    (letI := (sumCongr (finSumEquivOfCard hs) ρ₁ ρ₂).mulAction
    MulAction.orbit Gal(SeparableClosure K/K) i₀) = (s : Set (Fin n)) := by
  have hi₀' : i₀ ∈ Set.range (finSumEquivOfCard hs ∘ Sum.inl) := by
    rwa [range_finSumEquivOfCard_inl]
  obtain ⟨j₀, hj₀⟩ := hi₀'
  dsimp only [Function.comp_apply] at hj₀
  let := (sumCongr (finSumEquivOfCard hs) ρ₁ ρ₂).mulAction
  rw [← hj₀, (orbit_sumCongr_inl_eq_range_iff _ ρ₁ ρ₂ j₀).2 hρ₁,
    range_finSumEquivOfCard_inl]

private theorem ncard_orbit_sumCongr_finSumEquivOfCard
    (i₀ : Fin n) (s : ↥((Finset.univ.powersetCard m).filter (i₀ ∈ ·)))
    (ρ₁ : {ρ₁ : GaloisSet K m // ρ₁.IsTransitive}) (ρ₂ : GaloisSet K (n - m)) :
    (letI := (sumCongr (finSumEquivOfCard
      (Finset.mem_powersetCard.1 (Finset.mem_filter.1 s.2).1).2) ρ₁.1 ρ₂).mulAction
    (MulAction.orbit Gal(SeparableClosure K/K) i₀).ncard) = m := by
  have hs : s.1.card = m := (Finset.mem_powersetCard.1 (Finset.mem_filter.1 s.2).1).2
  have hi₀ : i₀ ∈ s.1 := (Finset.mem_filter.1 s.2).2
  let := (sumCongr (finSumEquivOfCard hs) ρ₁.1 ρ₂).mulAction
  rw [orbit_sumCongr_finSumEquivOfCard hs hi₀ ρ₁.1 ρ₁.2 ρ₂, Set.ncard_coe_finset, hs]

private theorem orbitCardEquiv_bijective (i₀ : Fin n) (m : ℕ) :
    Function.Bijective
      (fun p : ↥((Finset.univ.powersetCard m).filter (i₀ ∈ ·)) ×
          {ρ₁ : GaloisSet K m // ρ₁.IsTransitive} × GaloisSet K (n - m) ↦
        (⟨sumCongr (finSumEquivOfCard
            (Finset.mem_powersetCard.1 (Finset.mem_filter.1 p.1.2).1).2) p.2.1.1 p.2.2,
          ncard_orbit_sumCongr_finSumEquivOfCard i₀ p.1 p.2.1 p.2.2⟩ :
          {ρ : GaloisSet K n //
            letI := ρ.mulAction
            (MulAction.orbit Gal(SeparableClosure K/K) i₀).ncard = m})) := by
  constructor
  · -- Injectivity: the orbit of `i₀` recovers `s`, and `sumCongr_inj` recovers `(ρ₁, ρ₂)`.
    rintro ⟨s₁, ρ₁, ρ₂⟩ ⟨s₂, τ₁, τ₂⟩ h
    have hval : sumCongr (finSumEquivOfCard
          (Finset.mem_powersetCard.1 (Finset.mem_filter.1 s₁.2).1).2) ρ₁.1 ρ₂ =
        sumCongr (finSumEquivOfCard
          (Finset.mem_powersetCard.1 (Finset.mem_filter.1 s₂.2).1).2) τ₁.1 τ₂ :=
      congrArg Subtype.val h
    have hs_eq : s₁ = s₂ := by
      have horb₁ := orbit_sumCongr_finSumEquivOfCard
        (Finset.mem_powersetCard.1 (Finset.mem_filter.1 s₁.2).1).2
        (Finset.mem_filter.1 s₁.2).2 ρ₁.1 ρ₁.2 ρ₂
      have horb₂ := orbit_sumCongr_finSumEquivOfCard
        (Finset.mem_powersetCard.1 (Finset.mem_filter.1 s₂.2).1).2
        (Finset.mem_filter.1 s₂.2).2 τ₁.1 τ₁.2 τ₂
      rw [hval] at horb₁
      exact Subtype.ext (Finset.coe_inj.1 (horb₁.symm.trans horb₂))
    subst hs_eq
    obtain ⟨hρ₁, hρ₂⟩ := (sumCongr_inj _).1 hval
    exact Prod.ext rfl (Prod.ext (Subtype.ext hρ₁) hρ₂)
  · -- Surjectivity: take `s` to be the orbit of `i₀`, and split `ρ` along `s` via `sumCongrEquiv`.
    rintro ⟨ρ, hm⟩
    let := ρ.mulAction
    classical
    set s₀ : Finset (Fin n) := (MulAction.orbit Gal(SeparableClosure K/K) i₀).toFinset
    have hs₀_card : s₀.card = m := by
      rw [← Set.ncard_coe_finset, Set.coe_toFinset]
      exact hm
    have hi₀ : i₀ ∈ s₀ := Set.mem_toFinset.2 (MulAction.mem_orbit_self i₀)
    let s : ↥((Finset.univ.powersetCard m).filter (i₀ ∈ ·)) :=
      ⟨s₀, Finset.mem_filter.2 ⟨Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hs₀_card⟩, hi₀⟩⟩
    let e := finSumEquivOfCard hs₀_card
    have hinv : ∀ (σ : Gal(SeparableClosure K/K)) (i : Fin m),
        ρ.val σ (e (Sum.inl i)) ∈ Set.range (e ∘ Sum.inl) := by
      intro σ i
      rw [range_finSumEquivOfCard_inl]
      have hx : e (Sum.inl i) ∈ (s₀ : Set (Fin n)) := by
        rw [← range_finSumEquivOfCard_inl hs₀_card]
        exact ⟨i, rfl⟩
      rw [Set.coe_toFinset, MulAction.mem_orbit_iff] at hx ⊢
      obtain ⟨τ, hτ⟩ := hx
      exact ⟨σ * τ, by rw [mul_smul, hτ, smul_def]⟩
    let p := (sumCongrEquiv e).symm ⟨ρ, hinv⟩
    have hp : sumCongr e p.1 p.2 = ρ :=
      congrArg Subtype.val ((sumCongrEquiv e).apply_symm_apply ⟨ρ, hinv⟩)
    have hi₀' : i₀ ∈ Set.range (e ∘ Sum.inl) := by
      rw [range_finSumEquivOfCard_inl]
      exact hi₀
    obtain ⟨j₀, hj₀⟩ := hi₀'
    dsimp only [Function.comp_apply] at hj₀
    have htr : p.1.IsTransitive := by
      rw [← orbit_sumCongr_inl_eq_range_iff e p.1 p.2 j₀, hj₀,
        range_finSumEquivOfCard_inl, hp]
      exact (Set.coe_toFinset _).symm
    exact ⟨(s, ⟨p.1, htr⟩, p.2), Subtype.ext hp⟩

/-- **Decomposing a Galois set at the orbit of a base label.** The labelled Galois sets of size `n`
in which the orbit of `i₀` has cardinality `m` correspond to triples `(s, ρ₁, ρ₂)` consisting of an
`m`-element subset `s` of `Fin n` containing `i₀`, a transitive Galois set `ρ₁` of size `m`, and an
arbitrary Galois set `ρ₂` of size `n - m`. -/
def orbitCardEquiv (i₀ : Fin n) (m : ℕ) :
    ↥((Finset.univ.powersetCard m).filter (i₀ ∈ ·)) ×
      {ρ₁ : GaloisSet K m // ρ₁.IsTransitive} × GaloisSet K (n - m) ≃
    {ρ : GaloisSet K n //
      letI := ρ.mulAction
      (MulAction.orbit Gal(SeparableClosure K/K) i₀).ncard = m} :=
  Equiv.ofBijective
    (fun p ↦ ⟨sumCongr (finSumEquivOfCard
        (Finset.mem_powersetCard.1 (Finset.mem_filter.1 p.1.2).1).2) p.2.1.1 p.2.2,
      ncard_orbit_sumCongr_finSumEquivOfCard i₀ p.1 p.2.1 p.2.2⟩)
    (orbitCardEquiv_bijective i₀ m)

/-- `orbitCardEquiv i₀ m` sends `(s, ρ₁, ρ₂)` to `sumCongr` along `finSumEquivOfFinset`. -/
@[simp]
theorem coe_orbitCardEquiv_apply (i₀ : Fin n) (m : ℕ)
    (s : ↥((Finset.univ.powersetCard m).filter (i₀ ∈ ·)))
    (ρ₁ : {ρ₁ : GaloisSet K m // ρ₁.IsTransitive}) (ρ₂ : GaloisSet K (n - m)) :
    (orbitCardEquiv i₀ m (s, ρ₁, ρ₂) : GaloisSet K n) =
      sumCongr (finSumEquivOfFinset
        (Finset.mem_powersetCard.1 (Finset.mem_filter.1 s.2).1).2
        (by rw [Finset.card_compl, Fintype.card_fin,
          (Finset.mem_powersetCard.1 (Finset.mem_filter.1 s.2).1).2])) ρ₁.1 ρ₂ :=
  (rfl)

end OrbitCard

end TauCeti.GaloisSet
