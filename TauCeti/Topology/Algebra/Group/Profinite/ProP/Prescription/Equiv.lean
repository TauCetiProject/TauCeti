/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Prescription.Basic

/-!
# The prescription property under topological isomorphisms

The twisted coefficient system `I(χ)/pⁱ` and the prescription property of a continuous
`p`-adic character are intrinsic to the source topological group.  If `e : H ≃ₜ* G`, then
pullback along `e` identifies `I(χ)/pⁱ` with `I(χ ∘ e)/pⁱ`, compatibly with the
reductions between levels (at the coefficient level any continuous homomorphism `H →ₜ* G`
suffices).  The resulting equivalences on explicit continuous `H¹` show that
`χ` has the prescription property exactly when `χ ∘ e` does.

This transport is the naturality input needed to define the canonical character of a Demushkin
group using any of its normal-form presentations: uniqueness makes the transported character
independent of the chosen presentation.

## Main results

* `TauCeti.ZModTwist.compEquiv`: the coefficient equivalence
  `I(χ)/pⁱ ≃ I(χ ∘ f)/pⁱ` for a continuous homomorphism `f : H →ₜ* G`.
* `TauCeti.ZModTwist.subgroupSubtypeHom`: for a subgroup `U ≤ G`, the same equivalence along the
  inclusion of `U`, as a bijective `U`-equivariant homomorphism `I(χ)/pⁱ →+[U] I(χ|_U)/pⁱ`, where
  `U` acts on `I(χ)/pⁱ` through the inclusion.
* `TauCeti.ZModTwist.explicitH1CompEquiv`: the induced equivalence on explicit continuous `H¹`.
* `TauCeti.HasPrescriptionProperty.comp_equiv`: pullback along a topological group isomorphism
  preserves the prescription property.
* `TauCeti.hasPrescriptionProperty_comp_equiv_iff`: the corresponding equivalence.

## Reduction compatibility

`TauCeti.ZModTwist.explicitH1CompEquiv_reduce` states that the equivalences on `H¹` commute
with every reduction map `I(χ)/pⁱ → I(χ)/pʲ`.  Thus they identify the images of the reduction
maps, so the prescription property is unchanged by pullback along a topological isomorphism.
The related functoriality API is `TauCeti.ContCohomology.explicitMap1Equiv`,
`TauCeti.ContCohomology.explicitMap1_comp`, `TauCeti.ContCohomology.explicitMap1_congr_of_eq`,
and `TauCeti.ContCohomology.explicitCoeff1_eq_explicitMap1`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132,
  Proposition 6 and Theorem 4.
-/

public section

namespace TauCeti

open ContCohomology

universe u v

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G]
variable {H : Type v} [Group H] [TopologicalSpace H]

namespace ZModTwist

private theorem reduce_toAddMonoidHom_apply (χ : G →ₜ* ℤ_[p]ˣ) {i j : ℕ} (h : j ≤ i)
    (x : ZModTwist χ i) :
    (reduce χ h).toAddMonoidHom x = reduce χ h x :=
  rfl

private theorem reduce_toAddMonoidHom_smul (χ : G →ₜ* ℤ_[p]ˣ) {i j : ℕ} (h : j ≤ i)
    (g : G) (x : ZModTwist χ i) :
    (reduce χ h).toAddMonoidHom (g • x) = g • (reduce χ h).toAddMonoidHom x := by
  apply ZModTwist.ext
  simp only [reduce_toAddMonoidHom_apply, val_reduce, val_smul, map_mul]
  rw [castHom_charScalar χ h g]

/-- Pullback along a continuous group homomorphism `f` identifies the twisted coefficient modules
for `χ` and `χ ∘ f`.  On residue classes this is the identity. -/
noncomputable def compEquiv (f : H →ₜ* G) (χ : G →ₜ* ℤ_[p]ˣ) (i : ℕ) :
    ZModTwist χ i ≃+ ZModTwist (χ.comp f) i where
  toFun x := ⟨x.val⟩
  invFun x := ⟨x.val⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem compEquiv_apply (f : H →ₜ* G) (χ : G →ₜ* ℤ_[p]ˣ) (i : ℕ)
    (x : ZModTwist χ i) :
    (compEquiv f χ i x).val = x.val := (rfl)

@[simp]
theorem compEquiv_symm_apply (f : H →ₜ* G) (χ : G →ₜ* ℤ_[p]ˣ) (i : ℕ)
    (x : ZModTwist (χ.comp f) i) :
    ((compEquiv f χ i).symm x).val = x.val := (rfl)

/-- The coefficient equivalence for a pulled-back character is equivariant along the group
homomorphism. -/
@[simp]
theorem compEquiv_smul (f : H →ₜ* G) (χ : G →ₜ* ℤ_[p]ˣ) (i : ℕ) (h : H)
    (x : ZModTwist χ i) :
    compEquiv f χ i (f h • x) = h • compEquiv f χ i x := by
  apply ZModTwist.ext
  simp only [compEquiv_apply, val_smul, charScalar_apply, ContinuousMonoidHom.comp_toFun]

/-- The coefficient equivalence for a pulled-back character commutes with reduction between
levels. -/
@[simp]
theorem compEquiv_reduce (f : H →ₜ* G) (χ : G →ₜ* ℤ_[p]ˣ) {i j : ℕ} (h : j ≤ i)
    (x : ZModTwist χ i) :
    compEquiv f χ j (reduce χ h x) = reduce (χ.comp f) h (compEquiv f χ i x) := by
  apply ZModTwist.ext
  simp only [compEquiv_apply, val_reduce]

/-- Pullback along the inclusion of a subgroup `U ≤ G`, as a `U`-equivariant homomorphism
`I(χ)/pⁱ →+[U] I(χ|_U)/pⁱ`, where `U` acts on `I(χ)/pⁱ` through the inclusion. The underlying map is
`compEquiv (ContinuousMonoidHom.subgroupSubtype U) χ i`, the identity on residue classes
(`val_subgroupSubtypeHom`), so it is bijective (`subgroupSubtypeHom_bijective`). It is recorded as
an equivariant homomorphism because that is the form in which the coefficient maps of continuous
cohomology consume it. -/
noncomputable def subgroupSubtypeHom (U : Subgroup G) (χ : G →ₜ* ℤ_[p]ˣ) (i : ℕ) :
    ZModTwist χ i →+[U] ZModTwist (χ.comp (ContinuousMonoidHom.subgroupSubtype U)) i where
  toFun := compEquiv (ContinuousMonoidHom.subgroupSubtype U) χ i
  map_smul' u x := compEquiv_smul (ContinuousMonoidHom.subgroupSubtype U) χ i u x
  map_zero' := map_zero _
  map_add' := map_add _

theorem subgroupSubtypeHom_apply (U : Subgroup G) (χ : G →ₜ* ℤ_[p]ˣ) (i : ℕ) (x : ZModTwist χ i) :
    subgroupSubtypeHom U χ i x = compEquiv (ContinuousMonoidHom.subgroupSubtype U) χ i x := (rfl)

@[simp]
theorem val_subgroupSubtypeHom (U : Subgroup G) (χ : G →ₜ* ℤ_[p]ˣ) (i : ℕ) (x : ZModTwist χ i) :
    (subgroupSubtypeHom U χ i x).val = x.val := (rfl)

theorem subgroupSubtypeHom_bijective (U : Subgroup G) (χ : G →ₜ* ℤ_[p]ˣ) (i : ℕ) :
    Function.Bijective (subgroupSubtypeHom U χ i) :=
  (compEquiv (ContinuousMonoidHom.subgroupSubtype U) χ i).bijective

private theorem compEquiv_toAddMonoidHom_smul (f : H →ₜ* G) (χ : G →ₜ* ℤ_[p]ˣ) (i : ℕ)
    (h : H) (x : ZModTwist χ i) :
    (compEquiv f χ i).toAddMonoidHom (f h • x) = h • (compEquiv f χ i).toAddMonoidHom x :=
  compEquiv_smul f χ i h x

/-- Pullback along a topological group isomorphism identifies explicit continuous `H¹` with
twisted coefficients. -/
noncomputable def explicitH1CompEquiv (e : H ≃ₜ* G) (χ : G →ₜ* ℤ_[p]ˣ) (i : ℕ) :
    H1 G (ZModTwist χ i) ≃+ H1 H (ZModTwist (χ.comp (e : H →ₜ* G)) i) :=
  explicitMap1Equiv G (ZModTwist χ i) H
    (ZModTwist (χ.comp (e : H →ₜ* G)) i) e (compEquiv (e : H →ₜ* G) χ i)
    continuous_of_discreteTopology continuous_of_discreteTopology (compEquiv_smul (e : H →ₜ* G) χ i)

/-- The equivalence on explicit continuous `H¹` is pullback along the topological group
isomorphism and the coefficient equivalence `ZModTwist.compEquiv`. -/
@[simp]
theorem explicitH1CompEquiv_apply (e : H ≃ₜ* G) (χ : G →ₜ* ℤ_[p]ˣ) (i : ℕ)
    (x : H1 G (ZModTwist χ i)) :
    explicitH1CompEquiv e χ i x =
      explicitMap1 G (ZModTwist χ i) H
        (ZModTwist (χ.comp (e : H →ₜ* G)) i) e (compEquiv (e : H →ₜ* G) χ i).toAddMonoidHom
        continuous_of_discreteTopology (compEquiv_smul (e : H →ₜ* G) χ i) x :=
  explicitMap1Equiv_apply G (ZModTwist χ i) H
    (ZModTwist (χ.comp (e : H →ₜ* G)) i) e (compEquiv (e : H →ₜ* G) χ i)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (compEquiv_smul (e : H →ₜ* G) χ i) x

/-- The additive homomorphism underlying `explicitH1CompEquiv` is the compatible-pair pullback
map used to define it. -/
private theorem explicitH1CompEquiv_toAddMonoidHom (e : H ≃ₜ* G)
    (χ : G →ₜ* ℤ_[p]ˣ) (i : ℕ) :
    (explicitH1CompEquiv e χ i).toAddMonoidHom =
      explicitMap1 G (ZModTwist χ i) H
        (ZModTwist (χ.comp (e : H →ₜ* G)) i) e (compEquiv (e : H →ₜ* G) χ i).toAddMonoidHom
        continuous_of_discreteTopology (compEquiv_toAddMonoidHom_smul (e : H →ₜ* G) χ i) := by
  apply AddMonoidHom.ext
  exact explicitH1CompEquiv_apply e χ i

/-- The equivalences on explicit continuous `H¹` commute with reduction between the levels of
the twisted coefficient system. -/
theorem explicitH1CompEquiv_reduce (e : H ≃ₜ* G) (χ : G →ₜ* ℤ_[p]ˣ) {i j : ℕ}
    (h : j ≤ i) (x : H1 G (ZModTwist χ i)) :
    explicitH1CompEquiv e χ j
        (explicitCoeff1 G (ZModTwist χ i) (reduce χ h) continuous_of_discreteTopology x) =
      explicitCoeff1 H (ZModTwist (χ.comp (e : H →ₜ* G)) i)
        (reduce (χ.comp (e : H →ₜ* G)) h) continuous_of_discreteTopology
        (explicitH1CompEquiv e χ i x) := by
  have hrG' := reduce_toAddMonoidHom_smul χ h
  have hrH' (g : H) (m : ZModTwist (χ.comp (e : H →ₜ* G)) i) :
      (reduce (χ.comp (e : H →ₜ* G)) h).toAddMonoidHom (g • m) =
        g • (reduce (χ.comp (e : H →ₜ* G)) h).toAddMonoidHom m :=
    reduce_toAddMonoidHom_smul (χ.comp (e : H →ₜ* G)) h g m
  have hrG (g : G) (m : ZModTwist χ i) :
      (reduce χ h).toAddMonoidHom ((ContinuousMonoidHom.id G) g • m) =
        g • (reduce χ h).toAddMonoidHom m := by
    simpa only [ContinuousMonoidHom.coe_id, id_eq] using hrG' g m
  have hrH (g : H) (m : ZModTwist (χ.comp (e : H →ₜ* G)) i) :
      (reduce (χ.comp (e : H →ₜ* G)) h).toAddMonoidHom
          ((ContinuousMonoidHom.id H) g • m) =
        g • (reduce (χ.comp (e : H →ₜ* G)) h).toAddMonoidHom m := by
    simpa only [ContinuousMonoidHom.coe_id, id_eq] using hrH' g m
  have hcoeffG :
      explicitCoeff1 G (ZModTwist χ i) (reduce χ h) continuous_of_discreteTopology =
        explicitMap1 G (ZModTwist χ i) G (ZModTwist χ j) (ContinuousMonoidHom.id G)
          (reduce χ h).toAddMonoidHom continuous_of_discreteTopology hrG := by
    rw [explicitCoeff1_eq_explicitMap1]
    apply explicitMap1_congr_of_eq <;> rfl
  have hcoeffH :
      explicitCoeff1 H (ZModTwist (χ.comp (e : H →ₜ* G)) i)
          (reduce (χ.comp (e : H →ₜ* G)) h) continuous_of_discreteTopology =
        explicitMap1 H (ZModTwist (χ.comp (e : H →ₜ* G)) i) H
          (ZModTwist (χ.comp (e : H →ₜ* G)) j) (ContinuousMonoidHom.id H)
          (reduce (χ.comp (e : H →ₜ* G)) h).toAddMonoidHom continuous_of_discreteTopology
          hrH := by
    rw [explicitCoeff1_eq_explicitMap1]
    apply explicitMap1_congr_of_eq <;> rfl
  have hnat :
      (explicitH1CompEquiv e χ j).toAddMonoidHom.comp
          (explicitCoeff1 G (ZModTwist χ i) (reduce χ h) continuous_of_discreteTopology) =
        (explicitCoeff1 H (ZModTwist (χ.comp (e : H →ₜ* G)) i)
            (reduce (χ.comp (e : H →ₜ* G)) h) continuous_of_discreteTopology).comp
          (explicitH1CompEquiv e χ i).toAddMonoidHom := by
    rw [explicitH1CompEquiv_toAddMonoidHom, explicitH1CompEquiv_toAddMonoidHom,
      hcoeffG, hcoeffH,
      ← explicitMap1_comp (hcomp := fun k m => by
        simp only [ContinuousMonoidHom.comp_toFun, ContinuousMonoidHom.coe_id, id_eq,
          AddMonoidHom.comp_apply]
        rw [hrG', compEquiv_toAddMonoidHom_smul]),
      ← explicitMap1_comp (hcomp := fun k m => by
        simp only [ContinuousMonoidHom.comp_toFun, ContinuousMonoidHom.coe_id, id_eq,
          AddMonoidHom.comp_apply]
        rw [compEquiv_toAddMonoidHom_smul, hrH'])]
    apply explicitMap1_congr_of_eq
    · apply ContinuousMonoidHom.ext
      intro k
      rfl
    · apply AddMonoidHom.ext
      exact compEquiv_reduce (e : H →ₜ* G) χ h
  exact DFunLike.congr_fun hnat x

end ZModTwist

/-- Pullback along a topological group isomorphism preserves the prescription property. -/
theorem HasPrescriptionProperty.comp_equiv {e : H ≃ₜ* G} {χ : G →ₜ* ℤ_[p]ˣ}
    (hχ : HasPrescriptionProperty χ) :
    HasPrescriptionProperty (χ.comp (e : H →ₜ* G)) := by
  rw [hasPrescriptionProperty_iff]
  intro i hi y
  obtain ⟨x, hx⟩ := (hasPrescriptionProperty_iff χ).1 hχ i hi
    ((ZModTwist.explicitH1CompEquiv e χ 1).symm y)
  refine ⟨ZModTwist.explicitH1CompEquiv e χ i x, ?_⟩
  rw [← ZModTwist.explicitH1CompEquiv_reduce e χ hi x, hx,
    AddEquiv.apply_symm_apply]

/-- A character has the prescription property if and only if its pullback along a topological
group isomorphism does. -/
@[simp]
theorem hasPrescriptionProperty_comp_equiv_iff (e : H ≃ₜ* G) (χ : G →ₜ* ℤ_[p]ˣ) :
    HasPrescriptionProperty (χ.comp (e : H →ₜ* G)) ↔ HasPrescriptionProperty χ := by
  refine ⟨fun h ↦ ?_, HasPrescriptionProperty.comp_equiv⟩
  have h' := h.comp_equiv (e := e.symm)
  have heq : (χ.comp (e : H →ₜ* G)).comp (e.symm : G →ₜ* H) = χ := by
    apply ContinuousMonoidHom.ext
    intro g
    exact congrArg χ (e.apply_symm_apply g)
  rw [heq] at h'
  exact h'

end TauCeti
