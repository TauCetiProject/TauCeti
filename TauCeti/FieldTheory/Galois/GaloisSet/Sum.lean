/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.GaloisSet.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.Perm.Finite
import TauCeti.Algebra.GroupAction.OrbitRelQuotient

/-!
# Disjoint unions of labelled Galois sets

Given labelled Galois sets `ρ₁ : TauCeti.GaloisSet K m` and `ρ₂ : TauCeti.GaloisSet K l` together
with a bijection `e : Fin m ⊕ Fin l ≃ Fin n`, `TauCeti.GaloisSet.sumCongr e ρ₁ ρ₂` is the labelled
Galois set on `Fin n` acting through `ρ₁` on the left block `Set.range (e ∘ Sum.inl)` and through
`ρ₂` on the right block `Set.range (e ∘ Sum.inr)`.

Conversely, every labelled Galois set on `Fin n` whose permutations map `Set.range (e ∘ Sum.inl)`
into itself arises uniquely in this way (`TauCeti.GaloisSet.sumCongrEquiv`). This decomposes a
Galois set by peeling off an invariant union of orbits — in particular a single orbit — when
inductively computing masses by splitting type.

## Main definitions and results

* `TauCeti.GaloisSet.sumCongr`: transport the sum of two labelled Galois sets along a bijection
  `Fin m ⊕ Fin l ≃ Fin n`.
* `TauCeti.GaloisSet.sumCongr_injective`: injectivity in the pair `(ρ₁, ρ₂)` for a fixed `e`.
* `TauCeti.GaloisSet.stabilizer_sumCongr_inl`, `TauCeti.GaloisSet.stabilizer_sumCongr_inr`,
  `TauCeti.GaloisSet.orbit_sumCongr_inl`, and `TauCeti.GaloisSet.orbit_sumCongr_inr`: point
  stabilizers and orbits in each block.
* `TauCeti.GaloisSet.sumCongrEquiv`: equivalence between `GaloisSet K m × GaloisSet K l` and
  labelled Galois sets on `Fin n` leaving `Set.range (e ∘ Sum.inl)` invariant.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density
  of number field discriminants*, IMRN **2007**, rnm052, §2.
-/

public section

noncomputable section

namespace TauCeti.GaloisSet

variable {K : Type*} [Field K] {m l n : ℕ}

/-- The disjoint union of two labelled Galois sets `ρ₁` and `ρ₂`, transported to `Fin n` along a
bijection `e : Fin m ⊕ Fin l ≃ Fin n`. -/
def sumCongr (e : Fin m ⊕ Fin l ≃ Fin n) (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K l) :
    GaloisSet K n :=
  ⟨e.permCongrHom.toMonoidHom.comp
      ((Equiv.Perm.sumCongrHom (Fin m) (Fin l)).comp (ρ₁.val.prod ρ₂.val)), by
    rw [MonoidHom.ker_comp_of_injective _ _ e.permCongrHom.injective,
      MonoidHom.ker_comp_of_injective _ _ Equiv.Perm.sumCongrHom_injective,
      MonoidHom.ker_prod, Subgroup.coe_inf]
    exact ρ₁.property.inter ρ₂.property⟩

/-- Evaluating `sumCongr e ρ₁ ρ₂` transports the sum action of `ρ₁` and `ρ₂` along `e`. -/
theorem sumCongr_val_apply (e : Fin m ⊕ Fin l ≃ Fin n)
    (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K l)
    (σ : Gal(SeparableClosure K/K)) (i : Fin n) :
    (sumCongr e ρ₁ ρ₂).val σ i = e ((ρ₁.val σ).sumCongr (ρ₂.val σ) (e.symm i)) := by
  simp [sumCongr, Equiv.permCongr_apply]

/-- `sumCongr e ρ₁ ρ₂` acts on `e (Sum.inl j)` through `ρ₁`. -/
@[simp]
theorem sumCongr_val_apply_inl (e : Fin m ⊕ Fin l ≃ Fin n)
    (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K l)
    (σ : Gal(SeparableClosure K/K)) (j : Fin m) :
    (sumCongr e ρ₁ ρ₂).val σ (e (Sum.inl j)) = e (Sum.inl (ρ₁.val σ j)) := by
  simp [sumCongr_val_apply]

/-- `sumCongr e ρ₁ ρ₂` acts on `e (Sum.inr j)` through `ρ₂`. -/
@[simp]
theorem sumCongr_val_apply_inr (e : Fin m ⊕ Fin l ≃ Fin n)
    (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K l)
    (σ : Gal(SeparableClosure K/K)) (j : Fin l) :
    (sumCongr e ρ₁ ρ₂).val σ (e (Sum.inr j)) = e (Sum.inr (ρ₂.val σ j)) := by
  simp [sumCongr_val_apply]

/-- The kernel of `sumCongr e ρ₁ ρ₂` is the intersection of the kernels of `ρ₁` and `ρ₂`. -/
@[simp]
theorem ker_sumCongr (e : Fin m ⊕ Fin l ≃ Fin n) (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K l) :
    (sumCongr e ρ₁ ρ₂).val.ker = ρ₁.val.ker ⊓ ρ₂.val.ker := by
  rw [sumCongr, MonoidHom.ker_comp_of_injective _ _ e.permCongrHom.injective,
    MonoidHom.ker_comp_of_injective _ _ Equiv.Perm.sumCongrHom_injective,
    MonoidHom.ker_prod]

/-- For a fixed bijection `e`, `sumCongr e` is injective in the pair `(ρ₁, ρ₂)`. -/
theorem sumCongr_injective (e : Fin m ⊕ Fin l ≃ Fin n) :
    Function.Injective (Function.uncurry (sumCongr (K := K) e)) := by
  rintro ⟨ρ₁, ρ₂⟩ ⟨τ₁, τ₂⟩ h
  refine Prod.ext (ext fun σ j ↦ ?_) (ext fun σ j ↦ ?_)
  · have h1 := congrArg (fun ρ : GaloisSet K n ↦ ρ.val σ (e (Sum.inl j))) h
    simp only [Function.uncurry_apply_pair, sumCongr_val_apply_inl] at h1
    exact Sum.inl_injective (e.injective h1)
  · have h2 := congrArg (fun ρ : GaloisSet K n ↦ ρ.val σ (e (Sum.inr j))) h
    simp only [Function.uncurry_apply_pair, sumCongr_val_apply_inr] at h2
    exact Sum.inr_injective (e.injective h2)

/-- The stabilizer of `e (Sum.inl j)` in `sumCongr e ρ₁ ρ₂` is the stabilizer of `j` in `ρ₁`. -/
theorem stabilizer_sumCongr_inl (e : Fin m ⊕ Fin l ≃ Fin n)
    (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K l) (j : Fin m) :
    (letI := (sumCongr e ρ₁ ρ₂).mulAction
     MulAction.stabilizer Gal(SeparableClosure K/K) (e (Sum.inl j))) =
      (letI := ρ₁.mulAction
       MulAction.stabilizer Gal(SeparableClosure K/K) j) := by
  let := (sumCongr e ρ₁ ρ₂).mulAction
  let := ρ₁.mulAction
  exact TauCeti.MulAction.stabilizer_eq_of_injective (e ∘ Sum.inl)
    (e.injective.comp Sum.inl_injective) (fun σ x ↦ by simp) j

/-- The stabilizer of `e (Sum.inr j)` in `sumCongr e ρ₁ ρ₂` is the stabilizer of `j` in `ρ₂`. -/
theorem stabilizer_sumCongr_inr (e : Fin m ⊕ Fin l ≃ Fin n)
    (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K l) (j : Fin l) :
    (letI := (sumCongr e ρ₁ ρ₂).mulAction
     MulAction.stabilizer Gal(SeparableClosure K/K) (e (Sum.inr j))) =
      (letI := ρ₂.mulAction
       MulAction.stabilizer Gal(SeparableClosure K/K) j) := by
  let := (sumCongr e ρ₁ ρ₂).mulAction
  let := ρ₂.mulAction
  exact TauCeti.MulAction.stabilizer_eq_of_injective (e ∘ Sum.inr)
    (e.injective.comp Sum.inr_injective) (fun σ x ↦ by simp) j

/-- The orbit of `e (Sum.inl j)` in `sumCongr e ρ₁ ρ₂` is the image under `e ∘ Sum.inl` of the
orbit of `j` in `ρ₁`. -/
theorem orbit_sumCongr_inl (e : Fin m ⊕ Fin l ≃ Fin n)
    (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K l) (j : Fin m) :
    (letI := (sumCongr e ρ₁ ρ₂).mulAction
     MulAction.orbit Gal(SeparableClosure K/K) (e (Sum.inl j))) =
      (e ∘ Sum.inl) '' (letI := ρ₁.mulAction
                        MulAction.orbit Gal(SeparableClosure K/K) j) := by
  let := (sumCongr e ρ₁ ρ₂).mulAction
  let := ρ₁.mulAction
  ext x
  simp only [MulAction.mem_orbit_iff, Set.mem_image, Function.comp_apply, smul_def]
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨ρ₁.val σ j, ⟨σ, rfl⟩, (sumCongr_val_apply_inl e ρ₁ ρ₂ σ j).symm⟩
  · rintro ⟨k, ⟨σ, rfl⟩, rfl⟩
    exact ⟨σ, sumCongr_val_apply_inl e ρ₁ ρ₂ σ j⟩

/-- When `ρ₁` is transitive, the orbit of `e (Sum.inl j)` in `sumCongr e ρ₁ ρ₂` is the whole left
block `Set.range (e ∘ Sum.inl)`. -/
theorem orbit_sumCongr_inl_of_isTransitive (e : Fin m ⊕ Fin l ≃ Fin n)
    {ρ₁ : GaloisSet K m} (hρ₁ : ρ₁.IsTransitive) (ρ₂ : GaloisSet K l) (j : Fin m) :
    (letI := (sumCongr e ρ₁ ρ₂).mulAction
     MulAction.orbit Gal(SeparableClosure K/K) (e (Sum.inl j))) =
      Set.range (e ∘ Sum.inl) := by
  let := ρ₁.mulAction
  have : MulAction.IsPretransitive Gal(SeparableClosure K/K) (Fin m) := ρ₁.isTransitive_def.1 hρ₁
  rw [orbit_sumCongr_inl, MulAction.orbit_eq_univ, Set.image_univ]

/-- The orbit of `e (Sum.inr j)` in `sumCongr e ρ₁ ρ₂` is the image under `e ∘ Sum.inr` of the
orbit of `j` in `ρ₂`. -/
theorem orbit_sumCongr_inr (e : Fin m ⊕ Fin l ≃ Fin n)
    (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K l) (j : Fin l) :
    (letI := (sumCongr e ρ₁ ρ₂).mulAction
     MulAction.orbit Gal(SeparableClosure K/K) (e (Sum.inr j))) =
      (e ∘ Sum.inr) '' (letI := ρ₂.mulAction
                        MulAction.orbit Gal(SeparableClosure K/K) j) := by
  let := (sumCongr e ρ₁ ρ₂).mulAction
  let := ρ₂.mulAction
  ext x
  simp only [MulAction.mem_orbit_iff, Set.mem_image, Function.comp_apply, smul_def]
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨ρ₂.val σ j, ⟨σ, rfl⟩, (sumCongr_val_apply_inr e ρ₁ ρ₂ σ j).symm⟩
  · rintro ⟨k, ⟨σ, rfl⟩, rfl⟩
    exact ⟨σ, sumCongr_val_apply_inr e ρ₁ ρ₂ σ j⟩

/-- When `ρ₂` is transitive, the orbit of `e (Sum.inr j)` in `sumCongr e ρ₁ ρ₂` is the whole right
block `Set.range (e ∘ Sum.inr)`. -/
theorem orbit_sumCongr_inr_of_isTransitive (e : Fin m ⊕ Fin l ≃ Fin n)
    (ρ₁ : GaloisSet K m) {ρ₂ : GaloisSet K l} (hρ₂ : ρ₂.IsTransitive) (j : Fin l) :
    (letI := (sumCongr e ρ₁ ρ₂).mulAction
     MulAction.orbit Gal(SeparableClosure K/K) (e (Sum.inr j))) =
      Set.range (e ∘ Sum.inr) := by
  let := ρ₂.mulAction
  have : MulAction.IsPretransitive Gal(SeparableClosure K/K) (Fin l) := ρ₂.isTransitive_def.1 hρ₂
  rw [orbit_sumCongr_inr, MulAction.orbit_eq_univ, Set.image_univ]

/-- Every permutation in `sumCongr e ρ₁ ρ₂` maps the left block `Set.range (e ∘ Sum.inl)` into
itself. -/
theorem mapsTo_sumCongr_range_inl (e : Fin m ⊕ Fin l ≃ Fin n)
    (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K l) (σ : Gal(SeparableClosure K/K)) :
    Set.MapsTo ((sumCongr e ρ₁ ρ₂).val σ) (Set.range (e ∘ Sum.inl))
      (Set.range (e ∘ Sum.inl)) := by
  rintro _ ⟨j, rfl⟩
  exact ⟨ρ₁.val σ j, (sumCongr_val_apply_inl e ρ₁ ρ₂ σ j).symm⟩

/-- Pairs `(ρ₁, ρ₂)` of labelled Galois sets on `Fin m` and `Fin l` correspond via `sumCongr e` to
labelled Galois sets on `Fin n` whose permutations leave `Set.range (e ∘ Sum.inl)` invariant. -/
def sumCongrEquiv (e : Fin m ⊕ Fin l ≃ Fin n) :
    GaloisSet K m × GaloisSet K l ≃
      {ρ : GaloisSet K n //
        ∀ σ, Set.MapsTo (ρ.val σ) (Set.range (e ∘ Sum.inl)) (Set.range (e ∘ Sum.inl))} :=
  Equiv.ofBijective
    (fun p ↦ ⟨sumCongr e p.1 p.2, mapsTo_sumCongr_range_inl e p.1 p.2⟩)
    ⟨fun p q h ↦ sumCongr_injective e (congrArg Subtype.val h), by
      rintro ⟨ρ, hρ⟩
      let φ : Gal(SeparableClosure K/K) →* Equiv.Perm (Fin m ⊕ Fin l) :=
        e.symm.permCongrHom.toMonoidHom.comp ρ.val
      have hφ : ∀ σ, φ σ ∈ (Equiv.Perm.sumCongrHom (Fin m) (Fin l)).range := fun σ ↦ by
        refine Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl ?_
        rintro _ ⟨j, rfl⟩
        obtain ⟨j', hj'⟩ := hρ σ ⟨j, rfl⟩
        refine ⟨j', e.injective ?_⟩
        simpa [φ, Equiv.permCongr_apply] using hj'
      let ι := MulEquiv.ofBijective (Equiv.Perm.sumCongrHom (Fin m) (Fin l)).rangeRestrict
        ⟨fun _ _ h ↦ Equiv.Perm.sumCongrHom_injective (congrArg Subtype.val h),
         (Equiv.Perm.sumCongrHom (Fin m) (Fin l)).rangeRestrict_surjective⟩
      let ψ : Gal(SeparableClosure K/K) →* Equiv.Perm (Fin m) × Equiv.Perm (Fin l) :=
        ι.symm.toMonoidHom.comp (φ.codRestrict _ hφ)
      have hψ1 : ∀ {σ}, σ ∈ ρ.val.ker → ψ σ = 1 := fun {σ} hσ ↦ by
        rw [MonoidHom.mem_ker] at hσ
        have hφ1 : φ σ = 1 := by rw [MonoidHom.comp_apply, hσ, map_one]
        have hc : φ.codRestrict _ hφ σ = 1 := Subtype.ext hφ1
        simp [ψ, hc]
      let ρ₁ : GaloisSet K m := ⟨(MonoidHom.fst _ _).comp ψ, Subgroup.isOpen_mono
        (fun σ hσ ↦ MonoidHom.mem_ker.2 (by simp [hψ1 hσ])) ρ.property⟩
      let ρ₂ : GaloisSet K l := ⟨(MonoidHom.snd _ _).comp ψ, Subgroup.isOpen_mono
        (fun σ hσ ↦ MonoidHom.mem_ker.2 (by simp [hψ1 hσ])) ρ.property⟩
      refine ⟨(ρ₁, ρ₂), Subtype.ext (ext fun σ i ↦ ?_)⟩
      have hψ : Equiv.Perm.sumCongrHom (Fin m) (Fin l) (ψ σ) = φ σ :=
        congrArg Subtype.val (ι.apply_symm_apply (φ.codRestrict _ hφ σ))
      have hi := congrArg (fun p : Equiv.Perm (Fin m ⊕ Fin l) ↦ e (p (e.symm i))) hψ
      simpa [sumCongr_val_apply, ρ₁, ρ₂, φ, Equiv.permCongr_apply] using hi⟩

/-- The underlying Galois set of `sumCongrEquiv e (ρ₁, ρ₂)` is `sumCongr e ρ₁ ρ₂`. -/
@[simp]
theorem coe_sumCongrEquiv_apply (e : Fin m ⊕ Fin l ≃ Fin n)
    (p : GaloisSet K m × GaloisSet K l) :
    (sumCongrEquiv e p : GaloisSet K n) = sumCongr e p.1 p.2 :=
  (rfl)

end TauCeti.GaloisSet
