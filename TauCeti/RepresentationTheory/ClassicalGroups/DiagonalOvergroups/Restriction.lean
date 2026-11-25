/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.DiagonalOvergroups.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.SpecialLinear
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.CentralCharacter
public import TauCeti.RepresentationTheory.Tensor.External
import TauCeti.RepresentationTheory.Subrepresentation

/-!
# Restriction of external tensor products across diagonal overgroups of `GL`

Restricting `ρ.externalTensor σ` across the four diagonal overgroups of `GL ι R` separates the two
intermediate subgroups `scalarDiagonal` and `determinantEqual`:
1. **`diagonal ι R`:** `diagonalSubrepresentationOrderIso` identifies subrepresentations on
   `diagonal ι R` with `Subrepresentation (ρ.tprod σ)` by the identity on underlying submodules.
2. **`scalarDiagonal ι R`:** When scalar matrices act on `ρ` by scalars (e.g. by Schur's lemma, or
   with central exponent `∑ i, l i` from a weight `l`), the restriction is a character twist of
   `(ρ.tprod σ) ∘ sndProj`, preserving the subrepresentation lattice and all `Hom` multiplicities.
3. **`determinantEqual ι K`:** Over an algebraically closed field, for finite-dimensional
   representations `ρ` and `σ`, `(ρ.externalTensor σ)` restricted to `determinantEqual ι K` is
   irreducible iff `ρ` and `σ` are irreducible
   (`isIrreducible_externalTensor_comp_determinantEqual_iff`).

## References

* William Fulton and Joe Harris, *Representation Theory: A First Course*, Springer GTM 129, 1991,
  Lectures 6 and 15.
-/

public section

open Matrix TensorProduct

namespace TauCeti.DiagonalOvergroups

section Diagonal

variable {ι R V W : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
  [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
  (ρ : Representation R (GL ι R) V) (σ : Representation R (GL ι R) W)

/-- Pulling `ρ.externalTensor σ` back along `diagonalMap ι R` yields `ρ.tprod σ`. -/
@[simp] theorem externalTensor_comp_diagonalMap :
    (ρ.externalTensor σ).comp (diagonalMap ι R) = ρ.tprod σ := by
  ext g : 1; simp [Representation.tprod_apply]

/-- Pulling the `diagonal ι R` restriction back along `diagonalEquiv` yields `ρ.tprod σ`. -/
@[simp] theorem externalTensor_comp_diagonal_comp_diagonalEquiv :
    ((ρ.externalTensor σ).comp (diagonal ι R).subtype).comp
      ((diagonalEquiv (ι := ι) (R := R)) : GL ι R →* diagonal ι R) = ρ.tprod σ := by
  ext g : 1; simp [Representation.tprod_apply]

/-- **Subrepresentations of `ρ.externalTensor σ` on `diagonal ι R` match those of `ρ.tprod σ`.** -/
def diagonalSubrepresentationOrderIso :
    Subrepresentation ((ρ.externalTensor σ).comp (diagonal ι R).subtype) ≃o
      Subrepresentation (ρ.tprod σ) where
  toFun S := ⟨S.toSubmodule, fun g _ hz => by
    simpa [Representation.tprod_apply] using S.apply_mem_toSubmodule (diagonalEquiv g) hz⟩
  invFun S := ⟨S.toSubmodule, fun ⟨⟨g, h⟩, hp⟩ _ hz => by
    obtain rfl : g = h := mem_diagonal_iff.mp hp
    simpa [Representation.tprod_apply] using S.apply_mem_toSubmodule g hz⟩
  left_inv _ := Subrepresentation.toSubmodule_injective rfl
  right_inv _ := Subrepresentation.toSubmodule_injective rfl
  map_rel_iff' := by rfl

@[simp] theorem toSubmodule_diagonalSubrepresentationOrderIso
    (S : Subrepresentation ((ρ.externalTensor σ).comp (diagonal ι R).subtype)) :
    (diagonalSubrepresentationOrderIso ρ σ S).toSubmodule = S.toSubmodule := by rfl

@[simp] theorem toSubmodule_diagonalSubrepresentationOrderIso_symm
    (S : Subrepresentation (ρ.tprod σ)) :
    ((diagonalSubrepresentationOrderIso ρ σ).symm S).toSubmodule = S.toSubmodule := by rfl

end Diagonal

section ScalarDiagonal

variable {ι R V W U : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
  [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W] [AddCommMonoid U] [Module R U]
  (ρ : Representation R (GL ι R) V) (σ : Representation R (GL ι R) W)

private theorem externalTensor_scalar_mul_apply {u : Rˣ} {c : R}
    (hc : ∀ v : V, ρ (GeneralLinearGroup.scalar ι u) v = c • v) (g : GL ι R) :
    ρ.externalTensor σ (GeneralLinearGroup.scalar ι u * g, g) = c • (ρ.tprod σ) g :=
  TensorProduct.ext' fun v w => by
    simp [hc, TensorProduct.smul_tmul', Representation.tprod_apply]

/-- Pulling `ρ.externalTensor σ` back along `scalarDiagonalMap ι R` twists `(ρ.tprod σ) ∘ fst` by
`χ ∘ snd`. -/
theorem externalTensor_comp_scalarDiagonalMap_eq_charTwist (χ : Rˣ →* Rˣ)
    (hρ : ∀ (u : Rˣ) (v : V), ρ (GeneralLinearGroup.scalar ι u) v = (χ u : R) • v) :
    (ρ.externalTensor σ).comp (scalarDiagonalMap ι R) =
      Representation.charTwist (χ.comp (MonoidHom.snd (GL ι R) Rˣ))
        ((ρ.tprod σ).comp (MonoidHom.fst (GL ι R) Rˣ)) := by
  ext ⟨g, u⟩ : 1; simpa using externalTensor_scalar_mul_apply ρ σ (hρ u) g

/-- **Character-twist identification on `scalarDiagonal ι R`** for nonempty `ι`. -/
theorem externalTensor_comp_scalarDiagonal_eq_charTwist [Nonempty ι] (χ : Rˣ →* Rˣ)
    (hρ : ∀ (u : Rˣ) (v : V), ρ (GeneralLinearGroup.scalar ι u) v = (χ u : R) • v) :
    (ρ.externalTensor σ).comp (scalarDiagonal ι R).subtype =
      Representation.charTwist (χ.comp scalarProj) ((ρ.tprod σ).comp sndProj) := by
  ext q : 1
  obtain ⟨⟨g, u⟩, rfl⟩ := scalarDiagonalEquiv.surjective q
  simpa [scalarProj_apply_scalarDiagonalEquiv] using externalTensor_scalar_mul_apply ρ σ (hρ u) g

/-- Under `scalarDiagonalEquiv`, the restricted action is `(g, u) ↦ χ u • (ρ.tprod σ) g`. -/
theorem externalTensor_comp_scalarDiagonal_comp_scalarDiagonalEquiv [Nonempty ι] (χ : Rˣ →* Rˣ)
    (hρ : ∀ (u : Rˣ) (v : V), ρ (GeneralLinearGroup.scalar ι u) v = (χ u : R) • v) :
    ((ρ.externalTensor σ).comp (scalarDiagonal ι R).subtype).comp
      ((scalarDiagonalEquiv (ι := ι) (R := R)) : GL ι R × Rˣ →* scalarDiagonal ι R) =
      Representation.charTwist (χ.comp (MonoidHom.snd (GL ι R) Rˣ))
        ((ρ.tprod σ).comp (MonoidHom.fst (GL ι R) Rˣ)) := by
  ext ⟨g, u⟩ : 1; simpa using externalTensor_scalar_mul_apply ρ σ (hρ u) g

variable {ρ}

/-- **Identity-on-carrier subrepresentation lattice isomorphism for `scalarDiagonal ι R`.** -/
def scalarDiagonalSubrepresentationOrderIso
    (hρ : ∀ u : Rˣ, ∃ c : R, ∀ v : V, ρ (GeneralLinearGroup.scalar ι u) v = c • v) :
    Subrepresentation ((ρ.externalTensor σ).comp (scalarDiagonal ι R).subtype) ≃o
      Subrepresentation (ρ.tprod σ) where
  toFun S := ⟨S.toSubmodule, fun g _ hz => by
    simpa [Representation.tprod_apply] using
      S.apply_mem_toSubmodule ⟨(g, g), diagonal_le_scalarDiagonal (mem_diagonal_iff.mpr rfl)⟩ hz⟩
  invFun S := ⟨S.toSubmodule, fun ⟨p, hp⟩ z hz => by
    obtain ⟨u, hu⟩ := mem_scalarDiagonal_iff.mp hp
    obtain ⟨c, hc⟩ := hρ u
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, Subtype.coe_mk,
      (Prod.ext hu rfl : p = (GeneralLinearGroup.scalar ι u * p.2, p.2)),
      externalTensor_scalar_mul_apply ρ σ hc p.2, LinearMap.smul_apply]
    exact S.toSubmodule.smul_mem c (S.apply_mem_toSubmodule p.2 hz)⟩
  left_inv _ := Subrepresentation.toSubmodule_injective rfl
  right_inv _ := Subrepresentation.toSubmodule_injective rfl
  map_rel_iff' := by rfl

@[simp] theorem toSubmodule_scalarDiagonalSubrepresentationOrderIso
    (hρ : ∀ u : Rˣ, ∃ c : R, ∀ v : V, ρ (GeneralLinearGroup.scalar ι u) v = c • v)
    (S : Subrepresentation ((ρ.externalTensor σ).comp (scalarDiagonal ι R).subtype)) :
    (scalarDiagonalSubrepresentationOrderIso σ hρ S).toSubmodule = S.toSubmodule := by rfl

@[simp] theorem toSubmodule_scalarDiagonalSubrepresentationOrderIso_symm
    (hρ : ∀ u : Rˣ, ∃ c : R, ∀ v : V, ρ (GeneralLinearGroup.scalar ι u) v = c • v)
    (S : Subrepresentation (ρ.tprod σ)) :
    ((scalarDiagonalSubrepresentationOrderIso σ hρ).symm S).toSubmodule = S.toSubmodule := by rfl

/-- **Transport of intertwining maps from `GL ι R` to `scalarDiagonal ι R`.** -/
def scalarDiagonalIntertwiningMapLinearEquiv [Nonempty ι] (τ : Representation R (GL ι R) U)
    (χ : Rˣ →* Rˣ)
    (hρ : ∀ (u : Rˣ) (v : V), ρ (GeneralLinearGroup.scalar ι u) v = (χ u : R) • v) :
    Representation.IntertwiningMap τ (ρ.tprod σ) ≃ₗ[R]
      Representation.IntertwiningMap
        (Representation.charTwist (χ.comp scalarProj) (τ.comp sndProj))
        ((ρ.externalTensor σ).comp (scalarDiagonal ι R).subtype) where
  toFun f := ⟨f.toLinearMap, fun q => by
    obtain ⟨⟨g, u⟩, rfl⟩ := scalarDiagonalEquiv.surjective q
    ext x
    simpa [externalTensor_scalar_mul_apply ρ σ (hρ u) g, Representation.tprod_apply] using
      congrArg ((χ u : R) • ·) (LinearMap.congr_fun (f.isIntertwining' g) x)⟩
  invFun f := ⟨f.toLinearMap, fun g => by
    simpa [Representation.tprod_apply] using f.isIntertwining' (scalarDiagonalEquiv (g, 1))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := by rfl

@[simp]
theorem coe_scalarDiagonalIntertwiningMapLinearEquiv [Nonempty ι] (τ : Representation R (GL ι R) U)
    (χ : Rˣ →* Rˣ)
    (hρ : ∀ (u : Rˣ) (v : V), ρ (GeneralLinearGroup.scalar ι u) v = (χ u : R) • v)
    (f : Representation.IntertwiningMap τ (ρ.tprod σ)) :
    ⇑(scalarDiagonalIntertwiningMapLinearEquiv σ τ χ hρ f) = ⇑f := by rfl

@[simp] theorem coe_scalarDiagonalIntertwiningMapLinearEquiv_symm [Nonempty ι]
    (τ : Representation R (GL ι R) U) (χ : Rˣ →* Rˣ)
    (hρ : ∀ (u : Rˣ) (v : V), ρ (GeneralLinearGroup.scalar ι u) v = (χ u : R) • v)
    (f : Representation.IntertwiningMap
      (Representation.charTwist (χ.comp scalarProj) (τ.comp sndProj))
      ((ρ.externalTensor σ).comp (scalarDiagonal ι R).subtype)) :
    ⇑((scalarDiagonalIntertwiningMapLinearEquiv σ τ χ hρ).symm f) = ⇑f := by rfl

/-- **Equality of `Hom`-space multiplicities** between `ρ.tprod σ` and `scalarDiagonal ι R`. -/
theorem finrank_intertwiningMap_scalarDiagonal_eq [Nonempty ι] (τ : Representation R (GL ι R) U)
    (χ : Rˣ →* Rˣ)
    (hρ : ∀ (u : Rˣ) (v : V), ρ (GeneralLinearGroup.scalar ι u) v = (χ u : R) • v) :
    Module.finrank R
      (Representation.IntertwiningMap
        (Representation.charTwist (χ.comp scalarProj) (τ.comp sndProj))
        ((ρ.externalTensor σ).comp (scalarDiagonal ι R).subtype)) =
      Module.finrank R (Representation.IntertwiningMap τ (ρ.tprod σ)) :=
  (scalarDiagonalIntertwiningMapLinearEquiv σ τ χ hρ).symm.finrank_eq

end ScalarDiagonal

section Field

variable {ι K V W : Type*} [Fintype ι] [DecidableEq ι] [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Schur's-lemma specialization of `scalarDiagonalSubrepresentationOrderIso` over an algebraically
closed field. -/
noncomputable def scalarDiagonalSubrepresentationOrderIsoOfIsIrreducible [IsAlgClosed K]
    [FiniteDimensional K V] (ρ : Representation K (GL ι K) V) [ρ.IsIrreducible]
    (σ : Representation K (GL ι K) W) :
    Subrepresentation ((ρ.externalTensor σ).comp (scalarDiagonal ι K).subtype) ≃o
      Subrepresentation (ρ.tprod σ) :=
  scalarDiagonalSubrepresentationOrderIso σ fun u =>
    Representation.IsIrreducible.exists_forall_apply_eq_smul
      (ρ (GeneralLinearGroup.scalar ι u)) fun g v => by
        simpa only [map_mul, mul_apply_eq_comp, LinearMap.comp_apply] using
          congrArg (fun g' => ρ g' v) (GeneralLinearGroup.scalar_commute u g)

@[simp] theorem toSubmodule_scalarDiagonalSubrepresentationOrderIsoOfIsIrreducible [IsAlgClosed K]
    [FiniteDimensional K V] (ρ : Representation K (GL ι K) V) [ρ.IsIrreducible]
    (σ : Representation K (GL ι K) W)
    (S : Subrepresentation ((ρ.externalTensor σ).comp (scalarDiagonal ι K).subtype)) :
    (scalarDiagonalSubrepresentationOrderIsoOfIsIrreducible ρ σ S).toSubmodule = S.toSubmodule := by
  rfl

/-- Weight-character evaluation of `externalTensor_comp_scalarDiagonal_eq_charTwist`: an occurring
torus weight `l : Fin n → ℤ` gives central exponent `∑ i, l i`. -/
theorem externalTensor_comp_scalarDiagonal_eq_charTwist_of_weightSpace_ne_bot {n : ℕ} [NeZero n]
    {ρ : Representation K (GL (Fin n) K) V} [ρ.IsIrreducible]
    (σ : Representation K (GL (Fin n) K) W) {l : Fin n → ℤ} (hl : TauCeti.weightSpace ρ l ≠ ⊥) :
    (ρ.externalTensor σ).comp (scalarDiagonal (Fin n) K).subtype =
      Representation.charTwist ((zpowGroupHom (∑ i, l i)).comp scalarProj)
        ((ρ.tprod σ).comp sndProj) :=
  externalTensor_comp_scalarDiagonal_eq_charTwist ρ σ (zpowGroupHom (∑ i, l i))
    (TauCeti.apply_scalar_eq_zpow_smul_of_weightSpace_ne_bot hl)

private def slProdToDeterminantEqual :
    SpecialLinearGroup ι K × SpecialLinearGroup ι K →* determinantEqual ι K where
  toFun p := ⟨(SpecialLinearGroup.toGL p.1, SpecialLinearGroup.toGL p.2), by simp⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)

/-- **Irreducibility of `ρ.externalTensor σ` on `determinantEqual ι K`** for finite-dimensional
representations `ρ` and `σ` over an algebraically closed field. -/
@[simp] theorem isIrreducible_externalTensor_comp_determinantEqual_iff [IsAlgClosed K]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (ρ : Representation K (GL ι K) V) (σ : Representation K (GL ι K) W) :
    Representation.IsIrreducible ((ρ.externalTensor σ).comp (determinantEqual ι K).subtype) ↔
      ρ.IsIrreducible ∧ σ.IsIrreducible := by
  refine ⟨fun _ => ?_, fun ⟨hρ, hσ⟩ => ?_⟩
  · have h := Representation.IsIrreducible.of_comp (determinantEqual ι K).subtype
      (ρ := ρ.externalTensor σ)
    exact ⟨h.of_externalTensor_left, h.of_externalTensor_right⟩
  · have hSL : (Representation.externalTensor (ρ.comp SpecialLinearGroup.toGL)
        (σ.comp SpecialLinearGroup.toGL)).IsIrreducible :=
      Representation.isIrreducible_externalTensor _ _
        ((Representation.isIrreducible_comp_toGL_iff ρ).mpr hρ)
        ((Representation.isIrreducible_comp_toGL_iff σ).mpr hσ)
    have heq : ((ρ.externalTensor σ).comp (determinantEqual ι K).subtype).comp
        slProdToDeterminantEqual = Representation.externalTensor (ρ.comp SpecialLinearGroup.toGL)
          (σ.comp SpecialLinearGroup.toGL) := by ext p : 1; simp [slProdToDeterminantEqual]
    have : Representation.IsIrreducible (((ρ.externalTensor σ).comp
        (determinantEqual ι K).subtype).comp slProdToDeterminantEqual) := heq ▸ hSL
    exact Representation.IsIrreducible.of_comp slProdToDeterminantEqual
      (ρ := (ρ.externalTensor σ).comp (determinantEqual ι K).subtype)

instance instIsIrreducibleExternalTensorCompDeterminantEqual [IsAlgClosed K]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (ρ : Representation K (GL ι K) V) (σ : Representation K (GL ι K) W)
    [ρ.IsIrreducible] [σ.IsIrreducible] :
    Representation.IsIrreducible ((ρ.externalTensor σ).comp (determinantEqual ι K).subtype) :=
  (isIrreducible_externalTensor_comp_determinantEqual_iff ρ σ).mpr ⟨‹_›, ‹_›⟩

end Field

end TauCeti.DiagonalOvergroups
