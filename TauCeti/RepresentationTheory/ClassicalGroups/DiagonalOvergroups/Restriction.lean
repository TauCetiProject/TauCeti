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

/-!
# Restriction of external tensor products across diagonal overgroups of `GL`

Given two representations `ρ` and `σ` of `GL ι R` on `V` and `W`, their external tensor product
`ρ.externalTensor σ` is a representation of `GL ι R × GL ι R` on `V ⊗[R] W`. Restricting it across
the four diagonal overgroups reveals the sharp representation-theoretic dichotomy between the two
proper intermediate subgroups `scalarDiagonal` and `determinantEqual`:

1. **Diagonal (`diagonal ι R`):** Pulling `ρ.externalTensor σ` back along `diagonalMap ι R` is the
   internal tensor product `ρ.tprod σ` (`externalTensor_comp_diagonalMap`), and restricting to
   `diagonal ι R` identifies the subrepresentation lattice with `Subrepresentation (ρ.tprod σ)` via
   the identity on underlying submodules (`diagonalSubrepresentationOrderIso`).
2. **Scalar-diagonal (`scalarDiagonal ι R`):** When scalar matrices `scalar ι u` act on `V` through
   a unit character `χ : Rˣ →* Rˣ`, the restriction to `scalarDiagonal ι R` (for nonempty `ι`) is
   the character twist `charTwist (χ.comp scalarProj) ((ρ.tprod σ).comp sndProj)`
   (`externalTensor_comp_scalarDiagonal_eq_charTwist`), and for an irreducible `GL (Fin n) K`
   representation with an occurring torus weight `l` that character is `u ↦ u ^ ∑ i, l i`.
   Even over an arbitrary commutative ring and arbitrary finite index type `ι`, whenever scalar
   matrices act on `V` by scalars, `scalarDiagonalSubrepresentationOrderIso` identifies
   `Subrepresentation ((ρ.externalTensor σ).comp (scalarDiagonal ι R).subtype)` with
   `Subrepresentation (ρ.tprod σ)` by the identity on underlying submodules, and
   `scalarDiagonalIntertwiningMapLinearEquiv` transports all intertwining-map spaces (hence all
   `Hom`-space multiplicities) identically.
3. **Equal-determinant (`determinantEqual ι K`):** Over an algebraically closed field `K`,
   `determinantEqual ι K` contains `SL ι K × SL ι K`. Because finite-dimensional irreducible
   representations of `GL ι K` remain irreducible on `SL ι K`
   (`Representation.isIrreducible_comp_toGL_iff`) and external tensor products of irreducibles are
   irreducible (`Representation.isIrreducible_externalTensor`), `(ρ.externalTensor σ)` restricted
   to `determinantEqual ι K` is irreducible if and only if both `ρ` and `σ` are irreducible
   (`isIrreducible_externalTensor_comp_determinantEqual_iff`) — with no rationality or
   characteristic hypothesis, and across all ranks including `0` and `1`.

## Main definitions

* `TauCeti.DiagonalOvergroups.diagonalSubrepresentationOrderIso`: identity-on-carrier order
  isomorphism between subrepresentations on `diagonal ι R` and subrepresentations of `ρ.tprod σ`.
* `TauCeti.DiagonalOvergroups.scalarDiagonalSubrepresentationOrderIso`: identity-on-carrier order
  isomorphism between subrepresentations on `scalarDiagonal ι R` and subrepresentations of
  `ρ.tprod σ` when scalar matrices act on `ρ` by scalars.
* `TauCeti.DiagonalOvergroups.scalarDiagonalSubrepresentationOrderIsoOfIsIrreducible`: Schur
  specialization for a finite-dimensional irreducible `ρ` over an algebraically closed field.
* `TauCeti.DiagonalOvergroups.scalarDiagonalIntertwiningMapLinearEquiv`: `R`-linear isomorphism
  transporting `IntertwiningMap τ (ρ.tprod σ)` to `scalarDiagonal ι R` with matching scalar
  character, preserving the underlying linear map.

## Main results

* `TauCeti.DiagonalOvergroups.externalTensor_comp_scalarDiagonal_eq_charTwist` and
  `TauCeti.DiagonalOvergroups.externalTensor_comp_scalarDiagonal_eq_charTwist_of_weightSpace_ne_bot`
  give the character-twist formula on `scalarDiagonal ι R` and evaluate its central exponent as
  `∑ i, l i` from an occurring torus weight `l`.
* `TauCeti.DiagonalOvergroups.finrank_intertwiningMap_scalarDiagonal_eq`: equality of `Hom`-space
  multiplicities between `diagonal` and `scalarDiagonal`.
* `TauCeti.DiagonalOvergroups.isIrreducible_externalTensor_comp_determinantEqual_iff`:
  irreducibility of `(ρ.externalTensor σ)` on `determinantEqual ι K` over an algebraically closed
  field.

## References

* William Fulton and Joe Harris, *Representation Theory: A First Course*, Springer GTM 129, 1991,
  Lectures 6 and 15.
-/

public section

open Matrix TensorProduct

namespace TauCeti.DiagonalOvergroups

/-! ### Restriction to the diagonal subgroup -/

section Diagonal

variable {ι R V W : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
  [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
  (ρ : Representation R (GL ι R) V) (σ : Representation R (GL ι R) W)

/-- Pulling `ρ.externalTensor σ` back along `diagonalMap ι R` yields the internal tensor product
`ρ.tprod σ`. -/
@[simp]
theorem externalTensor_comp_diagonalMap :
    (ρ.externalTensor σ).comp (diagonalMap ι R) = ρ.tprod σ := by
  ext g : 1
  simp [Representation.tprod_apply]

/-- Pulling the `diagonal ι R` restriction back along `diagonalEquiv` yields `ρ.tprod σ`. -/
@[simp]
theorem externalTensor_comp_diagonal_comp_diagonalEquiv :
    ((ρ.externalTensor σ).comp (diagonal ι R).subtype).comp
      ((diagonalEquiv (ι := ι) (R := R)) : GL ι R →* diagonal ι R) = ρ.tprod σ := by
  ext g : 1
  simp [Representation.tprod_apply]

/-- **Subrepresentations of `ρ.externalTensor σ` on `diagonal ι R` are the subrepresentations of
`ρ.tprod σ`**, by the identity on underlying submodules. -/
def diagonalSubrepresentationOrderIso :
    Subrepresentation ((ρ.externalTensor σ).comp (diagonal ι R).subtype) ≃o
      Subrepresentation (ρ.tprod σ) where
  toFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule g z hz := by
        simpa [Representation.tprod_apply] using S.apply_mem_toSubmodule (diagonalEquiv g) hz }
  invFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := by
        rintro ⟨⟨g, h⟩, hp⟩ z hz
        obtain rfl : g = h := mem_diagonal_iff.mp hp
        simpa [Representation.tprod_apply] using S.apply_mem_toSubmodule g hz }
  left_inv _ := Subrepresentation.toSubmodule_injective rfl
  right_inv _ := Subrepresentation.toSubmodule_injective rfl
  map_rel_iff' := Iff.rfl

@[simp]
theorem toSubmodule_diagonalSubrepresentationOrderIso
    (S : Subrepresentation ((ρ.externalTensor σ).comp (diagonal ι R).subtype)) :
    (diagonalSubrepresentationOrderIso ρ σ S).toSubmodule = S.toSubmodule :=
  (rfl)

@[simp]
theorem toSubmodule_diagonalSubrepresentationOrderIso_symm
    (S : Subrepresentation (ρ.tprod σ)) :
    ((diagonalSubrepresentationOrderIso ρ σ).symm S).toSubmodule = S.toSubmodule :=
  (rfl)

end Diagonal

/-! ### Restriction to the scalar-diagonal subgroup and multiplicity transport -/

section ScalarDiagonal

variable {ι R V W U : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
  [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W] [AddCommMonoid U] [Module R U]
  (ρ : Representation R (GL ι R) V) (σ : Representation R (GL ι R) W)

private theorem externalTensor_scalar_mul_apply {u : Rˣ} {c : R}
    (hc : ∀ v : V, ρ (GeneralLinearGroup.scalar ι u) v = c • v) (g : GL ι R) :
    ρ.externalTensor σ (GeneralLinearGroup.scalar ι u * g, g) = c • (ρ.tprod σ) g := by
  refine TensorProduct.ext' fun v w => ?_
  simp only [Representation.externalTensor_apply_tmul, map_mul, mul_apply_eq_comp, hc,
    TensorProduct.smul_tmul', LinearMap.smul_apply, Representation.tprod_apply,
    TensorProduct.map_tmul]

/-- Pulling `ρ.externalTensor σ` back along `scalarDiagonalMap ι R` twists `(ρ.tprod σ) ∘ fst` by
the scalar character `χ ∘ snd`. -/
theorem externalTensor_comp_scalarDiagonalMap_eq_charTwist (χ : Rˣ →* Rˣ)
    (hρ : ∀ (u : Rˣ) (v : V), ρ (GeneralLinearGroup.scalar ι u) v = (χ u : R) • v) :
    (ρ.externalTensor σ).comp (scalarDiagonalMap ι R) =
      Representation.charTwist (χ.comp (MonoidHom.snd (GL ι R) Rˣ))
        ((ρ.tprod σ).comp (MonoidHom.fst (GL ι R) Rˣ)) := by
  ext ⟨g, u⟩ : 1
  simpa using externalTensor_scalar_mul_apply ρ σ (hρ u) g

/-- **Explicit character-twist identification on `scalarDiagonal ι R`** for nonempty `ι`: when
scalar matrices act on `ρ` through `χ : Rˣ →* Rˣ`, the restriction of `ρ.externalTensor σ` to
`scalarDiagonal ι R` is `(ρ.tprod σ) ∘ sndProj` twisted by `χ ∘ scalarProj`. -/
theorem externalTensor_comp_scalarDiagonal_eq_charTwist [Nonempty ι] (χ : Rˣ →* Rˣ)
    (hρ : ∀ (u : Rˣ) (v : V), ρ (GeneralLinearGroup.scalar ι u) v = (χ u : R) • v) :
    (ρ.externalTensor σ).comp (scalarDiagonal ι R).subtype =
      Representation.charTwist (χ.comp scalarProj) ((ρ.tprod σ).comp sndProj) := by
  ext q : 1
  obtain ⟨⟨g, u⟩, rfl⟩ := scalarDiagonalEquiv.surjective q
  simpa [scalarProj_apply_scalarDiagonalEquiv] using externalTensor_scalar_mul_apply ρ σ (hρ u) g

/-- Under `scalarDiagonalEquiv : GL ι R × Rˣ ≃* scalarDiagonal ι R`, the restricted external tensor
product is `(g, u) ↦ χ u • (ρ.tprod σ) g`. -/
theorem externalTensor_comp_scalarDiagonal_comp_scalarDiagonalEquiv [Nonempty ι] (χ : Rˣ →* Rˣ)
    (hρ : ∀ (u : Rˣ) (v : V), ρ (GeneralLinearGroup.scalar ι u) v = (χ u : R) • v) :
    ((ρ.externalTensor σ).comp (scalarDiagonal ι R).subtype).comp
      ((scalarDiagonalEquiv (ι := ι) (R := R)) : GL ι R × Rˣ →* scalarDiagonal ι R) =
      Representation.charTwist (χ.comp (MonoidHom.snd (GL ι R) Rˣ))
        ((ρ.tprod σ).comp (MonoidHom.fst (GL ι R) Rˣ)) := by
  ext ⟨g, u⟩ : 1
  simpa using externalTensor_scalar_mul_apply ρ σ (hρ u) g

variable {ρ}

/-- **Identity-on-carrier subrepresentation lattice isomorphism for `scalarDiagonal ι R`.**
Whenever scalar matrices act on `ρ` by scalars (across all finite index types `ι`, including
`IsEmpty ι`), restricting `ρ.externalTensor σ` to `scalarDiagonal ι R` yields the exact same
invariant submodules as the diagonal internal tensor product `ρ.tprod σ`. -/
def scalarDiagonalSubrepresentationOrderIso
    (hρ : ∀ u : Rˣ, ∃ c : R, ∀ v : V, ρ (GeneralLinearGroup.scalar ι u) v = c • v) :
    Subrepresentation ((ρ.externalTensor σ).comp (scalarDiagonal ι R).subtype) ≃o
      Subrepresentation (ρ.tprod σ) where
  toFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule g z hz := by
        simpa [Representation.tprod_apply] using
          S.apply_mem_toSubmodule
            ⟨(g, g), diagonal_le_scalarDiagonal (mem_diagonal_iff.mpr rfl)⟩ hz }
  invFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := by
        rintro ⟨p, hp⟩ z hz
        obtain ⟨u, hu⟩ := mem_scalarDiagonal_iff.mp hp
        obtain ⟨c, hc⟩ := hρ u
        have hp' : p = (GeneralLinearGroup.scalar ι u * p.2, p.2) := Prod.ext hu rfl
        change (ρ.externalTensor σ p) z ∈ S.toSubmodule
        rw [hp', externalTensor_scalar_mul_apply ρ σ hc p.2, LinearMap.smul_apply]
        exact S.toSubmodule.smul_mem c (S.apply_mem_toSubmodule p.2 hz) }
  left_inv _ := Subrepresentation.toSubmodule_injective rfl
  right_inv _ := Subrepresentation.toSubmodule_injective rfl
  map_rel_iff' := Iff.rfl

@[simp]
theorem toSubmodule_scalarDiagonalSubrepresentationOrderIso
    (hρ : ∀ u : Rˣ, ∃ c : R, ∀ v : V, ρ (GeneralLinearGroup.scalar ι u) v = c • v)
    (S : Subrepresentation ((ρ.externalTensor σ).comp (scalarDiagonal ι R).subtype)) :
    (scalarDiagonalSubrepresentationOrderIso σ hρ S).toSubmodule = S.toSubmodule :=
  (rfl)

@[simp]
theorem toSubmodule_scalarDiagonalSubrepresentationOrderIso_symm
    (hρ : ∀ u : Rˣ, ∃ c : R, ∀ v : V, ρ (GeneralLinearGroup.scalar ι u) v = c • v)
    (S : Subrepresentation (ρ.tprod σ)) :
    ((scalarDiagonalSubrepresentationOrderIso σ hρ).symm S).toSubmodule = S.toSubmodule :=
  (rfl)

/-- **Transport of intertwining maps (and `Hom` multiplicities) from `GL ι R` to
`scalarDiagonal ι R`:** when scalar matrices act on `ρ` by `χ : Rˣ →* Rˣ` and `τ` is extended to
`scalarDiagonal ι R` with the same central character `χ ∘ scalarProj`, the spaces of intertwining
maps are canonically `R`-linearly isomorphic via the identity on underlying linear maps. -/
def scalarDiagonalIntertwiningMapLinearEquiv [Nonempty ι] (τ : Representation R (GL ι R) U)
    (χ : Rˣ →* Rˣ)
    (hρ : ∀ (u : Rˣ) (v : V), ρ (GeneralLinearGroup.scalar ι u) v = (χ u : R) • v) :
    Representation.IntertwiningMap τ (ρ.tprod σ) ≃ₗ[R]
      Representation.IntertwiningMap
        (Representation.charTwist (χ.comp scalarProj) (τ.comp sndProj))
        ((ρ.externalTensor σ).comp (scalarDiagonal ι R).subtype) where
  toFun f :=
    { toLinearMap := f.toLinearMap
      isIntertwining' q := by
        obtain ⟨⟨g, u⟩, rfl⟩ := scalarDiagonalEquiv.surjective q
        simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, coe_scalarDiagonalEquiv_apply,
          Representation.charTwist_apply, sndProj_apply, scalarProj_apply_scalarDiagonalEquiv,
          externalTensor_scalar_mul_apply ρ σ (hρ u) g, LinearMap.comp_smul, LinearMap.smul_comp,
          f.isIntertwining' g] }
  invFun f :=
    { toLinearMap := f.toLinearMap
      isIntertwining' g := by
        have hq := f.isIntertwining' (scalarDiagonalEquiv (g, 1))
        simpa [Representation.tprod_apply] using hq }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_scalarDiagonalIntertwiningMapLinearEquiv [Nonempty ι] (τ : Representation R (GL ι R) U)
    (χ : Rˣ →* Rˣ)
    (hρ : ∀ (u : Rˣ) (v : V), ρ (GeneralLinearGroup.scalar ι u) v = (χ u : R) • v)
    (f : Representation.IntertwiningMap τ (ρ.tprod σ)) :
    ⇑(scalarDiagonalIntertwiningMapLinearEquiv σ τ χ hρ f) = ⇑f :=
  (rfl)

@[simp]
theorem coe_scalarDiagonalIntertwiningMapLinearEquiv_symm [Nonempty ι]
    (τ : Representation R (GL ι R) U) (χ : Rˣ →* Rˣ)
    (hρ : ∀ (u : Rˣ) (v : V), ρ (GeneralLinearGroup.scalar ι u) v = (χ u : R) • v)
    (f : Representation.IntertwiningMap
      (Representation.charTwist (χ.comp scalarProj) (τ.comp sndProj))
      ((ρ.externalTensor σ).comp (scalarDiagonal ι R).subtype)) :
    ⇑((scalarDiagonalIntertwiningMapLinearEquiv σ τ χ hρ).symm f) = ⇑f :=
  (rfl)

/-- **Equality of `Hom`-space multiplicities** between the diagonal tensor product `ρ.tprod σ` and
the `scalarDiagonal ι R` restriction. -/
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

/-! ### Schur and weight specializations over fields -/

section Field

variable {ι K V W : Type*} [Fintype ι] [DecidableEq ι] [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Over an algebraically closed field, Schur's lemma supplies the scalar central character of any
finite-dimensional irreducible `ρ` automatically, giving a hypothesis-free identity-on-carrier
`OrderIso` between subrepresentations on `scalarDiagonal ι K` and subrepresentations of
`ρ.tprod σ`. -/
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

@[simp]
theorem toSubmodule_scalarDiagonalSubrepresentationOrderIsoOfIsIrreducible [IsAlgClosed K]
    [FiniteDimensional K V] (ρ : Representation K (GL ι K) V) [ρ.IsIrreducible]
    (σ : Representation K (GL ι K) W)
    (S : Subrepresentation ((ρ.externalTensor σ).comp (scalarDiagonal ι K).subtype)) :
    (scalarDiagonalSubrepresentationOrderIsoOfIsIrreducible ρ σ S).toSubmodule = S.toSubmodule :=
  (rfl)

/-- For a representation `ρ` of `GL (Fin n) K` (`n ≠ 0`) that is irreducible and has an occurring
torus weight `l : Fin n → ℤ`, the `scalarDiagonal` restriction is `(ρ.tprod σ) ∘ sndProj` twisted
by `u ↦ u ^ (∑ i, l i)` along `scalarProj`. -/
theorem externalTensor_comp_scalarDiagonal_eq_charTwist_of_weightSpace_ne_bot {n : ℕ} [NeZero n]
    {ρ : Representation K (GL (Fin n) K) V} [ρ.IsIrreducible]
    (σ : Representation K (GL (Fin n) K) W) {l : Fin n → ℤ} (hl : TauCeti.weightSpace ρ l ≠ ⊥) :
    (ρ.externalTensor σ).comp (scalarDiagonal (Fin n) K).subtype =
      Representation.charTwist ((zpowGroupHom (∑ i, l i)).comp scalarProj)
        ((ρ.tprod σ).comp sndProj) :=
  externalTensor_comp_scalarDiagonal_eq_charTwist ρ σ (zpowGroupHom (∑ i, l i))
    (TauCeti.apply_scalar_eq_zpow_smul_of_weightSpace_ne_bot hl)

/-! ### Irreducibility on `determinantEqual` -/

private def slProdToDeterminantEqual :
    SpecialLinearGroup ι K × SpecialLinearGroup ι K →* determinantEqual ι K where
  toFun p := ⟨(SpecialLinearGroup.toGL p.1, SpecialLinearGroup.toGL p.2), by
    simp [mem_determinantEqual_iff]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' p q := Subtype.ext (by simp)

private theorem isIrreducible_of_comp {G₁ G₂ M : Type*} [Monoid G₁] [Monoid G₂]
    [AddCommGroup M] [Module K M] {τ : Representation K G₂ M} {f : G₁ →* G₂}
    (h : Representation.IsIrreducible (τ.comp f)) : τ.IsIrreducible := by
  have : Nontrivial M := h.nontrivial
  refine ⟨fun S => ?_⟩
  let T : Subrepresentation (τ.comp f) :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule g m hm := S.apply_mem_toSubmodule (f g) hm }
  refine (h.eq_bot_or_eq_top T).imp (fun hT => ?_) fun hT => ?_
  · exact Subrepresentation.toSubmodule_injective
      ((congrArg Subrepresentation.toSubmodule hT).trans Subrepresentation.toSubmodule_bot.symm)
  · exact Subrepresentation.toSubmodule_injective
      ((congrArg Subrepresentation.toSubmodule hT).trans Subrepresentation.toSubmodule_top.symm)

/-- **Irreducibility of `ρ.externalTensor σ` on `determinantEqual ι K`** over an algebraically
closed field: for finite-dimensional `V` and `W`, the restriction to `determinantEqual ι K` is
irreducible if and only if both `ρ` and `σ` are irreducible. No rationality or characteristic
assumption is needed, and rank `0` and rank `1` are included. -/
@[simp]
theorem isIrreducible_externalTensor_comp_determinantEqual_iff [IsAlgClosed K]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (ρ : Representation K (GL ι K) V) (σ : Representation K (GL ι K) W) :
    Representation.IsIrreducible ((ρ.externalTensor σ).comp (determinantEqual ι K).subtype) ↔
      ρ.IsIrreducible ∧ σ.IsIrreducible := by
  constructor
  · intro h
    have hext : (ρ.externalTensor σ).IsIrreducible := isIrreducible_of_comp h
    exact ⟨hext.of_externalTensor_left, hext.of_externalTensor_right⟩
  · rintro ⟨hρ, hσ⟩
    have hρSL : Representation.IsIrreducible (ρ.comp SpecialLinearGroup.toGL) :=
      (Representation.isIrreducible_comp_toGL_iff ρ).mpr hρ
    have hσSL : Representation.IsIrreducible (σ.comp SpecialLinearGroup.toGL) :=
      (Representation.isIrreducible_comp_toGL_iff σ).mpr hσ
    have hSLprod : (Representation.externalTensor (ρ.comp SpecialLinearGroup.toGL)
        (σ.comp SpecialLinearGroup.toGL)).IsIrreducible :=
      Representation.isIrreducible_externalTensor _ _ hρSL hσSL
    have heq : ((ρ.externalTensor σ).comp (determinantEqual ι K).subtype).comp
        slProdToDeterminantEqual =
        Representation.externalTensor (ρ.comp SpecialLinearGroup.toGL)
          (σ.comp SpecialLinearGroup.toGL) := by
      ext p : 1
      simp [slProdToDeterminantEqual]
    rw [← heq] at hSLprod
    exact isIrreducible_of_comp (f := slProdToDeterminantEqual) hSLprod

instance instIsIrreducibleExternalTensorCompDeterminantEqual [IsAlgClosed K]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (ρ : Representation K (GL ι K) V) (σ : Representation K (GL ι K) W)
    [ρ.IsIrreducible] [σ.IsIrreducible] :
    Representation.IsIrreducible ((ρ.externalTensor σ).comp (determinantEqual ι K).subtype) :=
  (isIrreducible_externalTensor_comp_determinantEqual_iff ρ σ).mpr ⟨‹_›, ‹_›⟩

end Field

end TauCeti.DiagonalOvergroups
