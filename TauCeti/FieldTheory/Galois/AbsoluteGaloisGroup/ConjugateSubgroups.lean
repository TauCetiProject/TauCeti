/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
import TauCeti.FieldTheory.Normal.Embeddings
import Mathlib.GroupTheory.IndexNormal

/-!
# Fixing subgroups of conjugate embeddings

Two embeddings of a finite separable extension into a separable closure differ by an
automorphism of that closure. Their images are therefore conjugate intermediate fields, and
the Galois correspondence carries them to conjugate open subgroups of the absolute Galois
group. This is the subgroup comparison used when transporting restriction, corestriction,
and the Evens norm between different choices of embedding.

The automorphism carrying one embedding to the other comes from the transitive action on
embeddings in `TauCeti.FieldTheory.Normal.Embeddings`. Conjugacy of the fixing subgroups
follows from the corresponding stabilizer conjugacy theorem. The finer statement
`TauCeti.exists_galoisSubgroupEquiv_eq_conj` says that the two identifications of the absolute
Galois group of `L` with these subgroups differ by conjugation by a single element of `G_K`.

The same holds for any other way of realizing `G_L` inside `G_K`: if a ring isomorphism
`e : AlgebraicClosure L ≃+* AlgebraicClosure K` of algebraic closures extends the embedding `σ`,
then conjugation by `e` agrees with `TauCeti.absoluteGaloisGroupExtend K L σ` up to a single inner
automorphism of `G_K` (`TauCeti.exists_absoluteGaloisGroupExtend_eq_conj`). The isomorphism `e`
restricts to the separable closures because separability over `L` and over `K` agree, `L/K` being
separable.
-/

public section

namespace TauCeti

universe u v

variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]

/-- The open subgroups of `G_K` fixing two embedded copies of a finite extension `L/K`
are conjugate. The conjugating automorphism extends the natural `K`-algebra isomorphism
between the two copies of `L`. -/
theorem galoisSubgroup_conj [FiniteDimensional K L]
    (σ τ : L →ₐ[K] SeparableClosure K) :
    ∃ g : AbsoluteGaloisGroup K,
      (galoisSubgroup K L τ).toSubgroup =
        (galoisSubgroup K L σ).toSubgroup.map (MulAut.conj g).toMonoidHom := by
  simpa only [galoisSubgroup_toSubgroup] using
    AlgHom.fixingSubgroup_fieldRange_conj σ τ

/-- **The identifications of `G_L` with the subgroups cut out by two embeddings differ by an
inner automorphism of `G_K`**: for `K`-embeddings `σ τ : L →ₐ[K] Kˢ` there is `γ : G_K` with
`galoisSubgroupEquiv K L τ x = γ * galoisSubgroupEquiv K L σ x * γ⁻¹` for every `x : G_L`. The
element `γ` is the automorphism of `Kˢ` carrying the identification of separable closures attached
to `σ` to the one attached to `τ`. -/
theorem exists_galoisSubgroupEquiv_eq_conj [FiniteDimensional K L]
    (σ τ : L →ₐ[K] SeparableClosure K) :
    ∃ γ : AbsoluteGaloisGroup K, ∀ x : AbsoluteGaloisGroup L,
      (galoisSubgroupEquiv K L τ x : AbsoluteGaloisGroup K) =
        γ * galoisSubgroupEquiv K L σ x * γ⁻¹ := by
  let eσ := separableClosureRingEquiv K L σ
  let eτ := separableClosureRingEquiv K L τ
  -- `γ = eτ ∘ eσ⁻¹` fixes `K`, so it is an element of `G_K`.
  let γ : AbsoluteGaloisGroup K := AlgEquiv.ofRingEquiv (f := eσ.symm.trans eτ) fun c => by
    rw [RingEquiv.trans_apply, eσ.symm_apply_eq.2 (separableClosureRingEquiv_algebraMap_base
      K L σ c).symm, separableClosureRingEquiv_algebraMap_base]
  have hγ (w : SeparableClosure L) : γ (eσ w) = eτ w := by simp [γ]
  have hγ' (w : SeparableClosure L) : γ⁻¹ (eτ w) = eσ w := by
    rw [← hγ, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  refine ⟨γ, fun x => AlgEquiv.ext fun y => ?_⟩
  obtain ⟨w, rfl⟩ := eτ.surjective y
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hγ',
    galoisSubgroupEquiv_apply_separableClosureRingEquiv,
    galoisSubgroupEquiv_apply_separableClosureRingEquiv, hγ]

/-- **`absoluteGaloisGroupExtend` is conjugation by any extension of the embedding, up to an inner
automorphism of `G_K`.** Let `e : AlgebraicClosure L ≃+* AlgebraicClosure K` be a ring isomorphism
of algebraic closures that extends `σ : L →ₐ[K] Kˢ`. There is `γ : G_K` such that, whenever
`τ' ∈ G_K` corresponds to `τ ∈ G_L` under `e` (that is, `e ∘ τ = τ' ∘ e`), the image of `τ` under
`absoluteGaloisGroupExtend K L σ` is `γ * τ' * γ⁻¹`. The element `γ` is the automorphism of `Kˢ`
carrying the restriction of `e` to the separable closures to `separableClosureRingEquiv K L σ`. -/
theorem exists_absoluteGaloisGroupExtend_eq_conj [FiniteDimensional K L]
    (σ : L →ₐ[K] SeparableClosure K) (e : AlgebraicClosure L ≃+* AlgebraicClosure K)
    (he : ∀ x : L, e (algebraMap L (AlgebraicClosure L) x) = σ x) :
    ∃ γ : Field.absoluteGaloisGroup K, ∀ (τ : Field.absoluteGaloisGroup L)
      (τ' : Field.absoluteGaloisGroup K), (∀ y, e (τ.toRingEquiv y) = τ'.toRingEquiv (e y)) →
        absoluteGaloisGroupExtend K L σ τ = γ * τ' * γ⁻¹ := by
  -- Through `σ`, `e` is an `L`-algebra isomorphism, and `L/K` is separable, so `e` matches the
  -- separable closures of `L` and of `K`.
  have : Algebra.IsSeparable K L := Algebra.IsSeparable.of_algHom K (SeparableClosure K) σ
  let _ : Algebra L (AlgebraicClosure K) :=
    ((separableClosure K (AlgebraicClosure K)).val.toRingHom.comp σ.toRingHom).toAlgebra
  have : IsScalarTower K L (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun c ↦ by
      simp [RingHom.algebraMap_toAlgebra]
  let eL : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure K := AlgEquiv.ofRingEquiv (f := e) he
  have hmem (y : AlgebraicClosure L) : e y ∈ separableClosure K (AlgebraicClosure K) ↔
      y ∈ separableClosure L (AlgebraicClosure L) := by
    rw [← map_mem_separableClosure_iff (eL : AlgebraicClosure L →ₐ[L] AlgebraicClosure K),
      separableClosure.eq_restrictScalars_of_isSeparable K L, IntermediateField.mem_restrictScalars]
    -- `eL` is `e` as a function.
    exact Iff.rfl
  let eS : SeparableClosure L ≃+* SeparableClosure K :=
    { toFun := fun y ↦ ⟨e y, (hmem y).2 y.2⟩
      invFun := fun z ↦ ⟨e.symm z, (hmem _).1 (by simp)⟩
      left_inv := fun y ↦ Subtype.ext (e.symm_apply_apply y)
      right_inv := fun z ↦ Subtype.ext (e.apply_symm_apply z)
      map_mul' := fun a b ↦ Subtype.ext (map_mul e (a : AlgebraicClosure L) b)
      map_add' := fun a b ↦ Subtype.ext (map_add e (a : AlgebraicClosure L) b) }
  have heS (y : SeparableClosure L) : (eS y : AlgebraicClosure K) = e y := rfl
  let s := separableClosureRingEquiv K L σ
  -- `g = s ∘ eS⁻¹` fixes `K`, so it is an element of `G_K`.
  let g : AbsoluteGaloisGroup K := AlgEquiv.ofRingEquiv (f := eS.symm.trans s) fun c ↦ by
    have hc : eS (algebraMap K (SeparableClosure L) c) = algebraMap K (SeparableClosure K) c :=
      Subtype.ext <| by
        rw [heS, IsScalarTower.algebraMap_apply K L (SeparableClosure L),
          IntermediateField.coe_algebraMap_apply, he, σ.commutes]
    rw [RingEquiv.trans_apply, eS.symm_apply_eq.2 hc.symm,
      separableClosureRingEquiv_algebraMap_base]
  have hg (w : SeparableClosure L) : g (eS w) = s w := by simp [g]
  refine ⟨(absoluteGaloisGroupRestrictEquiv K).symm g, fun τ τ' hτ ↦ ?_⟩
  apply (absoluteGaloisGroupRestrictEquiv K).injective
  rw [map_mul, map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply]
  refine AlgEquiv.ext fun y ↦ ?_
  obtain ⟨w, rfl⟩ := s.surjective y
  have hg' : g⁻¹ (s w) = eS w := by rw [← hg, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  have hτ' : absoluteGaloisGroupRestrictEquiv K τ' (eS w) =
      eS (absoluteGaloisGroupRestrictEquiv L τ w) :=
    Subtype.ext <| (coe_absoluteGaloisGroupRestrictEquiv_apply K τ' (eS w)).trans <|
      (hτ w).symm.trans (congrArg e (coe_absoluteGaloisGroupRestrictEquiv_apply L τ w).symm)
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hg', hτ', hg,
    absoluteGaloisGroupExtend_apply_separableClosureRingEquiv]

/-- **The subgroup cut out by a quadratic extension is independent of its embedding.**
For a quadratic extension `L/K`, any two embeddings of `L` into the separable closure have the
same fixing subgroup of `G_K`. -/
theorem galoisSubgroup_eq_of_finrank_eq_two [FiniteDimensional K L]
    (σ τ : L →ₐ[K] SeparableClosure K) (hL : Module.finrank K L = 2) :
    galoisSubgroup K L σ = galoisSubgroup K L τ := by
  -- The two fixing subgroups are conjugate, and an index-two subgroup is normal.
  apply OpenSubgroup.toSubgroup_injective
  obtain ⟨g, hg⟩ := galoisSubgroup_conj K L σ τ
  let _ : (galoisSubgroup K L σ).toSubgroup.Normal :=
    Subgroup.normal_of_index_eq_two ((galoisSubgroup_index K L σ).trans hL)
  rw [hg]
  simpa only [MulEquiv.toMonoidHom_eq_coe] using
    (Subgroup.Normal.map_conj_eq (H := (galoisSubgroup K L σ).toSubgroup) g).symm

end TauCeti
