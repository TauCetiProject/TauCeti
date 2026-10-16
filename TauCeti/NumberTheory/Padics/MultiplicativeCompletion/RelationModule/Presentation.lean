/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Reciprocity
public import TauCeti.Topology.Algebra.Group.Profinite.Free.RelationModule.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Map
import TauCeti.NumberTheory.Padics.Module

/-!
# Relation-module surjections from presentations of local Galois groups

Let `L/K` be a finite Galois extension of `p`-adic fields, and let a free profinite group
surject onto `G_K`. Restricting this surjection to the kernel of its presentation of
`Gal(L/K)` gives a surjection onto `G_L`. Abelianizing and taking the maximal pro-`p`
quotient, Lyndon's isomorphism and local reciprocity identify the resulting map with a
`ℤ_p[Gal(L/K)]`-linear surjection from the relation module onto `A(L)`.

The theorem retains the map on classes of relations, so its kernel can subsequently be
studied through the original free presentation. It makes no assertion about projectivity
or the rank of that kernel. The number of generators is arbitrary.

## Main results

* `TauCeti.exists_relationModule_surjective_of_presentation`: a surjective free profinite
  presentation of `G_K` induces an equivariant surjection onto `A(L)`, with its values pinned
  through Lyndon's isomorphism and reciprocity.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  (5.6.6) and the proof of (7.4.2)(i).

The construction uses `freeProfiniteGroup.abelianizationProPEquivRelationModule` for
Lyndon's coordinates and `padicCompletionUnitsEquivAbelianizationProP` for reciprocity.
-/

public section

noncomputable section

namespace TauCeti

open Additive

variable (p : ℕ) [Fact p.Prime] (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Normal K L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [CharZero L]
  [Algebra ℚ_[p] K] [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] K L]
  [Module.Finite ℚ_[p] L] [ValuativeExtension ℚ_[p] L]
  {ι : Type} [Fintype ι] [DecidableEq ι] {g : ι → L ≃ₐ[K] L}
  (hg : Subgroup.closure (Set.range g) = ⊤) (j : L →ₐ[K] SeparableClosure K)
  (φ : freeProfiniteGroup ι →ₜ* AbsoluteGaloisGroup K)
  (hφ : ∀ x, j.restrictNormalHom (φ x) = freeProfiniteGroup.lift g x)

include hφ in
omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [CharZero L]
  [Fintype ι] [DecidableEq ι] in
private theorem presentation_ker_le_comap :
    (freeProfiniteGroup.lift g : freeProfiniteGroup ι →* L ≃ₐ[K] L).ker ≤
      (galoisSubgroup K L j).toSubgroup.comap φ.toMonoidHom := by
  intro r hr
  rw [Subgroup.mem_comap, galoisSubgroup_toSubgroup, ← j.ker_restrictNormalHom,
    MonoidHom.mem_ker]
  simpa using (hφ r).trans (MonoidHom.mem_ker.mp hr)

/-- A surjective free profinite presentation of `G_K` induces a `ℤ_p[Gal(L/K)]`-linear
surjection from the relation module onto the completed multiplicative group `A(L)`.
On a class of a relation `r`, the map is the class of `φ r` read through local reciprocity.
No hypothesis of tame ramification or bound on the number of generators is needed. -/
theorem exists_relationModule_surjective_of_presentation (hsurj : Function.Surjective φ) :
    ∃ β : MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g →ₗ[
        MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)] Additive ↑(padicCompletionUnits p L),
      Function.Surjective β ∧
      ∀ r : (freeProfiniteGroup.lift g : freeProfiniteGroup ι →* L ≃ₐ[K] L).ker,
        padicCompletionUnitsEquivAbelianizationProP p K L j
          (β (freeProfiniteGroup.abelianizationProPEquivRelationModule p hg
            (ofMul (abelianizationProPMk p _ _ r)))).toMul =
          abelianizationProPMk p (AbsoluteGaloisGroup K) (galoisSubgroup K L j).toSubgroup
            ⟨φ r, by
              rw [galoisSubgroup_toSubgroup, ← j.ker_restrictNormalHom,
                MonoidHom.mem_ker, hφ]
              exact MonoidHom.mem_ker.mp r.2⟩ := by
  let R := (freeProfiniteGroup.lift g : freeProfiniteGroup ι →* L ≃ₐ[K] L).ker
  let V := (galoisSubgroup K L j).toSubgroup
  have hRV : R ≤ V.comap φ.toMonoidHom := presentation_ker_le_comap K L j φ hφ
  -- Restriction to the presentation kernel is onto the arithmetic Galois subgroup.
  have hVR : V ≤ R.map φ.toMonoidHom := by
    intro v hv
    obtain ⟨r, rfl⟩ := hsurj v
    refine ⟨r, ?_, rfl⟩
    have hv' : j.restrictNormalHom (φ r) = 1 := by
      simpa only [V, galoisSubgroup_toSubgroup, ← j.ker_restrictNormalHom, MonoidHom.mem_ker]
        using hv
    exact MonoidHom.mem_ker.mpr (by simpa using (hφ r).symm.trans hv')
  let κ : abelianizationProP p (freeProfiniteGroup ι) R →ₜ*
      abelianizationProP p (AbsoluteGaloisGroup K) V :=
    ⟨abelianizationProPMap p φ.toMonoidHom φ.continuous hRV,
      continuous_abelianizationProPMap p φ.toMonoidHom φ.continuous hRV⟩
  have hκ : Function.Surjective κ :=
    abelianizationProPMap_surjective p φ.toMonoidHom φ.continuous hRV hVR
  have hκ_mk (r : R) : κ (abelianizationProPMk p _ R r) =
      abelianizationProPMk p _ V ⟨φ r, Subgroup.mem_comap.mp (hRV r.2)⟩ :=
    abelianizationProPMap_mk p φ.toMonoidHom φ.continuous hRV r
  let a := padicCompletionUnitsEquivAbelianizationProP p K L j
  let ψ : abelianizationProP p (freeProfiniteGroup ι) R →ₜ* ↑(padicCompletionUnits p L) :=
    (a.symm : _ →ₜ* _).comp κ
  have hψ : Function.Surjective ψ := a.symm.surjective.comp hκ
  have haψ (x) : a (ψ x) = κ x := by
    simp only [ψ, ContinuousMonoidHom.coe_comp, Function.comp_apply,
      ContinuousMonoidHom.coe_coe, ContinuousMulEquiv.apply_symm_apply]
  -- The pro-p module structure is p-adic exponentiation. Continuity makes ψ linear.
  have : CompactSpace R :=
    isCompact_iff_compactSpace.mp (isClosed_singleton.preimage
      (freeProfiniteGroup.lift g).continuous).isCompact
  let hA : IsProP p (abelianizationProP p (freeProfiniteGroup ι) R) :=
    isProP_maximalProPQuotient
  let _ := hA.module
  let _ := hA.continuousSMul_module
  let e := freeProfiniteGroup.abelianizationProPLinearEquivRelationModule p hg
  let b := (ψ.toMonoidHom.toAdditive.toPadicIntLinearMap p
    (continuous_ofMul.comp (ψ.continuous.comp continuous_toMul))).toLinearMap
  let β₀ := b.comp e.symm.toLinearMap
  have hβ₀ (m) : β₀ m = ofMul (ψ (e.symm m).toMul) := by
    simp [β₀, b]
  -- Equivariance on group elements promotes ℤ_p-linearity to group-algebra linearity.
  have hequiv (σ : L ≃ₐ[K] L) (m) :
      β₀ (MonoidAlgebra.single σ (1 : ℤ_[p]) • m) =
        MonoidAlgebra.single σ (1 : ℤ_[p]) • β₀ m := by
    obtain ⟨f, hf⟩ := freeProfiniteGroup.lift_surjective
      (by rw [hg]; exact dense_univ) σ
    have he (x : Additive (abelianizationProP p (freeProfiniteGroup ι) R)) :
        e ((f : freeProfiniteGroup ι ⧸ R) • x) =
          MonoidAlgebra.single σ (1 : ℤ_[p]) • e x := by
      simpa only [e, freeProfiniteGroup.abelianizationProPLinearEquivRelationModule_apply, hf] using
        freeProfiniteGroup.abelianizationProPEquivRelationModule_smul p hg f x
    have hinv : e.symm (MonoidAlgebra.single σ (1 : ℤ_[p]) • m) =
        (f : freeProfiniteGroup ι ⧸ R) • e.symm m := by
      apply e.injective
      simp only [e.apply_symm_apply, he]
    rw [hβ₀, hinv, Additive.toMul_smul, hβ₀]
    apply Additive.toMul.injective
    simp only [toMul_ofMul, padicCompletionUnits_single_smul, one_smul]
    apply a.injective
    have ha (z) : a (padicCompletionUnitsAut p L K σ z) =
        (φ f : AbsoluteGaloisGroup K ⧸ V) • a z := by
      simpa only [a, hφ, hf] using
        padicCompletionUnitsEquivAbelianizationProP_smul p K L j (φ f) z
    rw [haψ, ha, haψ]
    exact abelianizationProPMap_smul p φ.toMonoidHom φ.continuous hRV f _
  let β := MonoidAlgebra.equivariantOfLinearOfComm β₀ hequiv
  refine ⟨β, ?_, ?_⟩
  · intro z
    obtain ⟨x, hx⟩ := hψ z.toMul
    refine ⟨e (ofMul x), ?_⟩
    simp only [β, MonoidAlgebra.equivariantOfLinearOfComm_apply, hβ₀,
      e.symm_apply_apply, toMul_ofMul, hx, ofMul_toMul]
  · intro r
    simp only [β, MonoidAlgebra.equivariantOfLinearOfComm_apply]
    rw [hβ₀, ← freeProfiniteGroup.abelianizationProPLinearEquivRelationModule_apply,
      e.symm_apply_apply, toMul_ofMul]
    rw [toMul_ofMul, haψ, hκ_mk]

end TauCeti
