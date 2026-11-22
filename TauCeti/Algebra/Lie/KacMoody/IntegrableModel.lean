/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.KacMoody.Integrable
public import TauCeti.Algebra.Lie.Sl2.Weyl.Standard
import TauCeti.LinearAlgebra.Basis.Basic

/-!
# Concrete simple integrable Kac–Moody modules

This file constructs two explicit families of simple modules in `TauCeti.KacMoody.IsIntegrableO`
for a realization `R` of an integral square matrix `A`:

1. **One-dimensional modules (`TauCeti.KacMoody.OneDimModule`).** For an arbitrary index type `I`
   and any weight `lam : Dual K H` vanishing on all simple coroots (`∀ i, lam (R.coroot i) = 0`),
   `OneDimModule R lam hlam` realizes the one-dimensional simple `IsIntegrableO` module of weight
   `lam` (covering `[IsEmpty I]` via `isEmptyElim`, trivial modules, and one-dimensional affine
   characters vanishing on all simple coroots, and hence having level zero). Its weight support is
   identified by `OneDimModule.weightSpace_self` and `OneDimModule.weightSpace_eq_bot_of_ne`.
2. **Rank-one standard modules (`TauCeti.KacMoody.RankOneModule`).** For rank one (`[Unique I]`,
   `A default default = 2`), `RankOneModule R hA lam n hlam` equips `TauCeti.Sl2Std K n` over a
   field of characteristic zero (`[CharZero K]`) with an `Enveloping R`-action for any realization
   `H` and any weight `lam` with `lam (R.coroot default) = n`, giving an `(n + 1)`-dimensional
   simple `IsIntegrableO` module whose full weight support is determined by
   `RankOneModule.weightSpace_sub_nsmul_root` and `RankOneModule.weightSpace_eq_bot_of_forall_ne`,
   and on which `simpleWeylIntertwiner` agrees with `TauCeti.Sl2Std.weylUnit` and squares to
   `(-1) ^ n`.

## Main definitions

* `TauCeti.KacMoody.OneDimModule` (with `OneDimModule.equiv` and `OneDimModule.rep`): the
  one-dimensional simple `IsIntegrableO` module for any weight `lam` vanishing on all simple
  coroots.
* `TauCeti.KacMoody.RankOneModule` (with `RankOneModule.equiv`, `RankOneModule.basis`, and
  `RankOneModule.rep`): for `[Unique I]` and `A default default = 2`, the `(n + 1)`-dimensional
  module whose `Enveloping R`-action, simplicity, and `IsIntegrableO` structure are defined over
  `[CharZero K]`.

## Main results

* `TauCeti.KacMoody.OneDimModule.isSimpleModule`, `TauCeti.KacMoody.OneDimModule.isIntegrableO`,
  `TauCeti.KacMoody.OneDimModule.weightSpace_self`, and
  `TauCeti.KacMoody.OneDimModule.weightSpace_eq_bot_of_ne`: simplicity, integrability in category
  `O`, and full weight-support characterization for `OneDimModule`.
* `TauCeti.KacMoody.RankOneModule.isSimpleModule`, `TauCeti.KacMoody.RankOneModule.isIntegrableO`,
  `TauCeti.KacMoody.RankOneModule.weightSpace_sub_nsmul_root`,
  `TauCeti.KacMoody.RankOneModule.weightSpace_eq_bot_of_forall_ne`,
  `TauCeti.KacMoody.RankOneModule.isNilpotent_positiveAction`,
  `TauCeti.KacMoody.RankOneModule.isNilpotent_negativeAction`,
  `TauCeti.KacMoody.RankOneModule.equiv_simpleWeylIntertwiner_apply`,
  `TauCeti.KacMoody.RankOneModule.simpleWeylIntertwiner_basis`, and
  `TauCeti.KacMoody.RankOneModule.simpleWeylIntertwiner_simpleWeylIntertwiner_apply`: simplicity,
  integrability, full weight-support characterization, nilpotence of the Chevalley actions, and
  the Weyl square `(-1) ^ n` on the rank-one models.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, 3rd ed., Cambridge University Press, 1990,
  §§3.5–3.8 and §10.1.
-/

public section

open Module

namespace TauCeti

namespace KacMoody

attribute [local instance 100] LieRing.ofAssociativeRing

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}

section OneDimModule

/-- **The one-dimensional module `K_λ`** for any weight `lam : Dual K H` vanishing on all simple
coroots (`∀ i : I, lam (R.coroot i) = 0`). On it, `cartanElement R x` acts by `lam x` and every
Chevalley generator `eᵢ`, `fᵢ` acts by `0`. When `I` is empty, the coroot-vanishing condition holds
vacuously via `isEmptyElim`. -/
def OneDimModule (_R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (_lam : Dual K H) (_hlam : ∀ i : I, _lam (_R.coroot i) = 0) : Type _ := K

namespace OneDimModule

variable (R : CartanRealization (A.map (Int.cast : ℤ → K)) H) (lam : Dual K H)
  (hlam : ∀ i : I, lam (R.coroot i) = 0)

noncomputable instance : AddCommGroup (OneDimModule R lam hlam) := inferInstanceAs (AddCommGroup K)
noncomputable instance : Module K (OneDimModule R lam hlam) := inferInstanceAs (Module K K)
instance : FiniteDimensional K (OneDimModule R lam hlam) :=
  inferInstanceAs (FiniteDimensional K K)
instance : Nontrivial (OneDimModule R lam hlam) := inferInstanceAs (Nontrivial K)

/-- The canonical `K`-linear equivalence `OneDimModule R lam hlam ≃ₗ[K] K`. -/
noncomputable def equiv : OneDimModule R lam hlam ≃ₗ[K] K := LinearEquiv.refl K K

@[simp]
theorem finrank_eq_one : Module.finrank K (OneDimModule R lam hlam) = 1 :=
  Module.finrank_self K

private noncomputable def cartanHom : H →ₗ[K] Module.End K (OneDimModule R lam hlam) :=
  lam.smulRight 1

private theorem satisfiesRelations :
    SatisfiesRelations R (cartanHom R lam hlam) 0 0 where
  lie_cartan_cartan x y := by
    simp only [cartanHom, LinearMap.smulRight_apply, Ring.lie_def, mul_smul_comm,
      mul_one, mul_comm (lam x) (lam y), smul_smul, sub_self]
  lie_cartan_positive _ _ := by simp
  lie_cartan_negative _ _ := by simp
  lie_positive_negative_self i := by simp [cartanHom, hlam]
  lie_positive_negative_of_ne _ _ _ := by simp
  serre_positive _ _ := by simp
  serre_negative _ _ := by simp

/-- The `Enveloping R`-algebra representation defining the module action on
`OneDimModule R lam hlam`. -/
noncomputable def rep : Enveloping R →ₐ[K] Module.End K (OneDimModule R lam hlam) :=
  _root_.UniversalEnvelopingAlgebra.lift K (KacMoody.lift (satisfiesRelations R lam hlam))

noncomputable instance : Module (Enveloping R) (OneDimModule R lam hlam) :=
  Module.compHom (OneDimModule R lam hlam) (rep R lam hlam).toRingHom

/-- Scalar multiplication on `OneDimModule` is evaluation of `rep`. -/
theorem smul_def (u : Enveloping R) (v : OneDimModule R lam hlam) :
    u • v = rep R lam hlam u v := (rfl)

/-- Evaluating `rep` gives the `Enveloping R`-module scalar multiplication on `OneDimModule`. -/
@[simp]
theorem rep_apply (u : Enveloping R) (v : OneDimModule R lam hlam) :
    rep R lam hlam u v = u • v := (rfl)

instance : IsScalarTower K (Enveloping R) (OneDimModule R lam hlam) where
  smul_assoc c u v := by
    rw [smul_def, smul_def, AlgHom.map_smul_of_tower, LinearMap.smul_apply]

/-- On `OneDimModule R lam hlam`, `cartanAction` acts by scalar multiplication by `lam x`. -/
@[simp]
theorem cartanAction_apply_eq (x : H) (v : OneDimModule R lam hlam) :
    cartanAction R (OneDimModule R lam hlam) x v = lam x • v := by
  rw [cartanAction_apply, smul_def]
  simp [rep, cartanHom]

/-- On `OneDimModule R lam hlam`, `positiveAction` acts by `0`. -/
@[simp]
theorem positiveAction_apply_eq (i : I) (v : OneDimModule R lam hlam) :
    positiveAction R (OneDimModule R lam hlam) i v = 0 := by
  rw [positiveAction_apply, smul_def]
  simp [rep]

/-- On `OneDimModule R lam hlam`, `negativeAction` acts by `0`. -/
@[simp]
theorem negativeAction_apply_eq (i : I) (v : OneDimModule R lam hlam) :
    negativeAction R (OneDimModule R lam hlam) i v = 0 := by
  rw [negativeAction_apply, smul_def]
  simp [rep]

/-- Transporting `cartanAction` on `OneDimModule R lam hlam` along `equiv` multiplies by `lam x`. -/
theorem equiv_cartanAction_apply (x : H) (v : OneDimModule R lam hlam) :
    equiv R lam hlam (cartanAction R (OneDimModule R lam hlam) x v) =
      lam x * equiv R lam hlam v := by
  rw [cartanAction_apply_eq, map_smul, smul_eq_mul]

/-- Transporting `positiveAction` on `OneDimModule R lam hlam` along `equiv` gives `0`. -/
theorem equiv_positiveAction_apply (i : I) (v : OneDimModule R lam hlam) :
    equiv R lam hlam (positiveAction R (OneDimModule R lam hlam) i v) = 0 := by
  rw [positiveAction_apply_eq, map_zero]

/-- Transporting `negativeAction` on `OneDimModule R lam hlam` along `equiv` gives `0`. -/
theorem equiv_negativeAction_apply (i : I) (v : OneDimModule R lam hlam) :
    equiv R lam hlam (negativeAction R (OneDimModule R lam hlam) i v) = 0 := by
  rw [negativeAction_apply_eq, map_zero]

/-- Transporting a scalar `c : K` into `OneDimModule R lam hlam` via `equiv.symm` interacts with
`cartanAction` by multiplication by `lam x`. -/
theorem cartanAction_equiv_symm (x : H) (c : K) :
    cartanAction R (OneDimModule R lam hlam) x ((equiv R lam hlam).symm c) =
      (equiv R lam hlam).symm (lam x * c) := by
  rw [cartanAction_apply_eq, ← map_smul, smul_eq_mul]

/-- The `lam`-weight space of `OneDimModule R lam hlam` is the whole module `⊤`. -/
@[simp]
theorem weightSpace_self : weightSpace R (OneDimModule R lam hlam) lam = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [mem_weightSpace_iff]
  exact fun x ↦ cartanAction_apply_eq R lam hlam x v

/-- Every weight space of `OneDimModule R lam hlam` at a weight `μ ≠ lam` is trivial (`⊥`). -/
theorem weightSpace_eq_bot_of_ne {μ : Dual K H} (hμ : μ ≠ lam) :
    weightSpace R (OneDimModule R lam hlam) μ = ⊥ :=
  weightSpace_eq_bot_of_iSup_eq_top R (OneDimModule R lam hlam)
    (W := fun _ : Unit ↦ (⊤ : Submodule K (OneDimModule R lam hlam)))
    (w := fun _ : Unit ↦ lam) (fun _ ↦ by simp) (by simp) (by simpa using hμ)

/-- `OneDimModule R lam hlam` is a simple `Enveloping R`-module. -/
instance isSimpleModule : IsSimpleModule (Enveloping R) (OneDimModule R lam hlam) where
  eq_bot_or_eq_top P := by
    let : IsSimpleModule K (OneDimModule R lam hlam) := IsSimpleModule.congr (equiv R lam hlam)
    exact (eq_bot_or_eq_top (P.restrictScalars K)).imp
      (fun h ↦ Submodule.restrictScalars_injective K _ _ (by simpa using h))
      (fun h ↦ Submodule.restrictScalars_injective K _ _ (by simpa using h))

/-- `OneDimModule R lam hlam` lies in `IsIntegrableO R`. -/
theorem isIntegrableO : IsIntegrableO R (OneDimModule R lam hlam) where
  isWeightModule := by
    rw [isWeightModule_iff, eq_top_iff, ← weightSpace_self R lam hlam]
    exact le_iSup (weightSpace R (OneDimModule R lam hlam)) lam
  finiteDimensional_weightSpace _ := inferInstance
  exists_finset_rootLE := ⟨{lam}, fun μ hμ ↦ ⟨lam, Finset.mem_singleton_self lam, by
    by_contra hne
    refine hμ (weightSpace_eq_bot_of_ne R lam hlam fun h ↦ hne ?_)
    subst h
    exact CartanRealization.rootLE_refl μ⟩⟩
  locallyNilpotent_positiveAction i v := ⟨1, by simp⟩
  locallyNilpotent_negativeAction i v := ⟨1, by simp⟩

end OneDimModule

end OneDimModule

section RankOneModule

variable [Unique I]

/-- **The standard `(n + 1)`-dimensional rank-one Kac–Moody module `L(λ)`** for a single-node
index type `[Unique I]` with `A default default = 2` and `lam (R.coroot default) = n`. Over a
field of characteristic zero (`[CharZero K]`), it equips `TauCeti.Sl2Std K n` with the action of
`Enveloping R` for an arbitrary realization `H` of `A` (including realizations with central or
scaling directions), extending `Sl2Std.diag K n` from `R.coroot default` to all of `H` via `lam`,
yielding a simple module in `IsIntegrableO R`. -/
def RankOneModule (_R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (_hA : A default default = 2) (_lam : Dual K H) (n : ℕ)
    (_hlam : _lam (_R.coroot default) = n) : Type _ :=
  Sl2Std K n

namespace RankOneModule

variable (R : CartanRealization (A.map (Int.cast : ℤ → K)) H) (hA : A default default = 2)
  (lam : Dual K H) (n : ℕ) (hlam : lam (R.coroot default) = n)

noncomputable instance : AddCommGroup (RankOneModule R hA lam n hlam) :=
  inferInstanceAs (AddCommGroup (Sl2Std K n))

noncomputable instance : Module K (RankOneModule R hA lam n hlam) :=
  inferInstanceAs (Module K (Sl2Std K n))

noncomputable instance [CharZero K] : Module ℚ (RankOneModule R hA lam n hlam) :=
  inferInstanceAs (Module ℚ (Sl2Std K n))

instance : FiniteDimensional K (RankOneModule R hA lam n hlam) :=
  inferInstanceAs (Module.Finite K (Sl2Std K n))

instance : Nontrivial (RankOneModule R hA lam n hlam) :=
  inferInstanceAs (Nontrivial (Sl2Std K n))

/-- The canonical `K`-linear equivalence `RankOneModule R hA lam n hlam ≃ₗ[K] Sl2Std K n`. -/
noncomputable def equiv : RankOneModule R hA lam n hlam ≃ₗ[K] Sl2Std K n :=
  LinearEquiv.refl K (Sl2Std K n)

/-- The coordinate basis of `RankOneModule R hA lam n hlam` transported from `Sl2Std.basis K n`. -/
noncomputable def basis : Module.Basis (Fin (n + 1)) K (RankOneModule R hA lam n hlam) :=
  (Sl2Std.basis K n).map (equiv R hA lam n hlam).symm

@[simp]
theorem equiv_basis (k : Fin (n + 1)) :
    equiv R hA lam n hlam (basis R hA lam n hlam k) = Sl2Std.basis K n k := by
  simp [basis]

@[simp]
theorem finrank_eq : Module.finrank K (RankOneModule R hA lam n hlam) = n + 1 :=
  Sl2Std.finrank_eq

section CharZero

variable [CharZero K]

private noncomputable def sl2CartanHom : H →ₗ[K] Module.End K (Sl2Std K n) :=
  (lam - ((n : K) * 2⁻¹) • R.root default).smulRight 1 +
    ((2⁻¹ : K) • R.root default).smulRight (Sl2Std.diag K n)

private theorem sl2CartanHom_coroot (hA : A default default = 2) :
    sl2CartanHom R lam n (R.coroot default) =
      ((lam (R.coroot default) - (n : K)) • (1 : Module.End K (Sl2Std K n))) + Sl2Std.diag K n := by
  have hrc : R.root default (R.coroot default) = 2 := R.root_coroot_eq_two hA
  simp only [sl2CartanHom, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, hrc, smul_eq_mul]
  rw [mul_assoc (n : K) 2⁻¹ 2, inv_mul_cancel₀ two_ne_zero, mul_one, one_smul]

private theorem half_mul_two (a : K) : (2⁻¹ * a) * 2 = a := by
  rw [mul_assoc, mul_comm a 2, ← mul_assoc, inv_mul_cancel₀ two_ne_zero, one_mul]

private noncomputable def sl2Rep (hA : A default default = 2) (hlam : lam (R.coroot default) = n) :
    Enveloping R →ₐ[K] Module.End K (Sl2Std K n) :=
  _root_.UniversalEnvelopingAlgebra.lift K <| KacMoody.lift <|
    { lie_cartan_cartan := fun x y ↦ by
        simp only [sl2CartanHom, LinearMap.add_apply, LinearMap.smulRight_apply, lie_add, add_lie,
          lie_smul, smul_lie, Ring.lie_def (1 : Module.End K (Sl2Std K n)),
          Ring.lie_def _ (1 : Module.End K (Sl2Std K n)), mul_one, one_mul, sub_self, lie_self,
          smul_zero, add_zero]
      lie_cartan_positive := fun x j ↦ by
        rw [Unique.eq_default j]
        simp only [sl2CartanHom, LinearMap.add_apply, LinearMap.smulRight_apply, add_lie, smul_lie,
          LinearMap.smul_apply, smul_eq_mul]
        have h1 : ⁅(1 : Module.End K (Sl2Std K n)), Sl2Std.raise K n⁆ = 0 := by
          simp [Ring.lie_def]
        rw [h1, Sl2Std.lie_diag_raise, smul_zero, zero_add, smul_smul, half_mul_two]
      lie_cartan_negative := fun x j ↦ by
        rw [Unique.eq_default j]
        simp only [sl2CartanHom, LinearMap.add_apply, LinearMap.smulRight_apply, add_lie, smul_lie,
          LinearMap.smul_apply, smul_eq_mul]
        have h1 : ⁅(1 : Module.End K (Sl2Std K n)), Sl2Std.lower K n⁆ = 0 := by
          simp [Ring.lie_def]
        rw [h1, Sl2Std.lie_diag_lower, smul_zero, zero_add, smul_neg, smul_smul, half_mul_two]
      lie_positive_negative_self := fun i ↦ by
        rw [Unique.eq_default i, Sl2Std.lie_raise_lower, sl2CartanHom_coroot R lam n hA, hlam,
          sub_self, zero_smul, zero_add]
      lie_positive_negative_of_ne := fun i j hij ↦ absurd (Subsingleton.elim i j) hij
      serre_positive := fun _ _ ↦ by rw [lie_self, map_zero]
      serre_negative := fun _ _ ↦ by rw [lie_self, map_zero] :
        SatisfiesRelations R (sl2CartanHom R lam n) (fun _ ↦ Sl2Std.raise K n)
          (fun _ ↦ Sl2Std.lower K n) }

/-- The `Enveloping R`-algebra representation defining the module action on
`RankOneModule R hA lam n hlam`. -/
noncomputable def rep : Enveloping R →ₐ[K] Module.End K (RankOneModule R hA lam n hlam) :=
  ((equiv R hA lam n hlam).symm.conjAlgEquiv K).toAlgHom.comp (sl2Rep R lam n hA hlam)

noncomputable instance : Module (Enveloping R) (RankOneModule R hA lam n hlam) :=
  Module.compHom (RankOneModule R hA lam n hlam) (rep R hA lam n hlam).toRingHom

/-- Scalar multiplication on `RankOneModule` is evaluation of `rep`. -/
theorem smul_def (u : Enveloping R) (v : RankOneModule R hA lam n hlam) :
    u • v = rep R hA lam n hlam u v := (rfl)

/-- Evaluating `rep` gives the `Enveloping R`-module scalar multiplication on `RankOneModule`. -/
@[simp]
theorem rep_apply (u : Enveloping R) (v : RankOneModule R hA lam n hlam) :
    rep R hA lam n hlam u v = u • v := (rfl)

instance : IsScalarTower K (Enveloping R) (RankOneModule R hA lam n hlam) where
  smul_assoc c u v := by
    rw [smul_def, smul_def, AlgHom.map_smul_of_tower, LinearMap.smul_apply]

/-- Under `equiv`, the Chevalley generator `eᵢ` acts on `RankOneModule R hA lam n hlam` as
`Sl2Std.raise K n`. -/
theorem positiveAction_eq (i : I) :
    positiveAction R (RankOneModule R hA lam n hlam) i =
      (equiv R hA lam n hlam).symm.conjAlgEquiv K (Sl2Std.raise K n) := by
  ext v
  rw [positiveAction_apply, smul_def]
  simp [rep, sl2Rep]

/-- Under `equiv`, the Chevalley generator `fᵢ` acts on `RankOneModule R hA lam n hlam` as
`Sl2Std.lower K n`. -/
theorem negativeAction_eq (i : I) :
    negativeAction R (RankOneModule R hA lam n hlam) i =
      (equiv R hA lam n hlam).symm.conjAlgEquiv K (Sl2Std.lower K n) := by
  ext v
  rw [negativeAction_apply, smul_def]
  simp [rep, sl2Rep]

/-- `positiveAction R (RankOneModule R hA lam n hlam) i` is nilpotent. -/
theorem isNilpotent_positiveAction (i : I) :
    IsNilpotent (positiveAction R (RankOneModule R hA lam n hlam) i) :=
  ⟨n + 1, by rw [positiveAction_eq, ← map_pow, Sl2Std.raise_pow_eq_zero, map_zero]⟩

/-- `negativeAction R (RankOneModule R hA lam n hlam) i` is nilpotent. -/
theorem isNilpotent_negativeAction (i : I) :
    IsNilpotent (negativeAction R (RankOneModule R hA lam n hlam) i) :=
  ⟨n + 1, by rw [negativeAction_eq, ← map_pow, Sl2Std.lower_pow_eq_zero, map_zero]⟩

private theorem cartanAction_eq_sl2CartanHom (x : H) :
    cartanAction R (RankOneModule R hA lam n hlam) x =
      (equiv R hA lam n hlam).symm.conjAlgEquiv K (sl2CartanHom R lam n x) := by
  ext v
  rw [cartanAction_apply, smul_def]
  simp [rep, sl2Rep]

/-- The Cartan action of an arbitrary `x : H` on `RankOneModule R hA lam n hlam`. -/
theorem cartanAction_eq (x : H) :
    cartanAction R (RankOneModule R hA lam n hlam) x =
      (equiv R hA lam n hlam).symm.conjAlgEquiv K
        ((lam x - (n : K) * 2⁻¹ * R.root default x) • (1 : Module.End K (Sl2Std K n)) +
          (2⁻¹ * R.root default x) • Sl2Std.diag K n) := by
  rw [cartanAction_eq_sl2CartanHom]
  simp [sl2CartanHom]

/-- Under `equiv`, the simple coroot `R.coroot i` acts on `RankOneModule R hA lam n hlam` as
`Sl2Std.diag K n`. -/
theorem cartanAction_coroot (i : I) :
    cartanAction R (RankOneModule R hA lam n hlam) (R.coroot i) =
      (equiv R hA lam n hlam).symm.conjAlgEquiv K (Sl2Std.diag K n) := by
  rw [Unique.eq_default i, cartanAction_eq_sl2CartanHom, sl2CartanHom_coroot R lam n hA,
    hlam, sub_self, zero_smul, zero_add]

/-- Transporting `positiveAction` on `RankOneModule R hA lam n hlam` across `equiv` yields
`Sl2Std.raise K n`. -/
@[simp]
theorem equiv_positiveAction_apply (i : I) (v : RankOneModule R hA lam n hlam) :
    equiv R hA lam n hlam (positiveAction R (RankOneModule R hA lam n hlam) i v) =
      Sl2Std.raise K n (equiv R hA lam n hlam v) := by
  rw [positiveAction_eq]
  simp [LinearEquiv.conjAlgEquiv_apply]

/-- Transporting `negativeAction` on `RankOneModule R hA lam n hlam` across `equiv` yields
`Sl2Std.lower K n`. -/
@[simp]
theorem equiv_negativeAction_apply (i : I) (v : RankOneModule R hA lam n hlam) :
    equiv R hA lam n hlam (negativeAction R (RankOneModule R hA lam n hlam) i v) =
      Sl2Std.lower K n (equiv R hA lam n hlam v) := by
  rw [negativeAction_eq]
  simp [LinearEquiv.conjAlgEquiv_apply]

/-- Pointwise evaluation of the Cartan action of an arbitrary `x : H` under `equiv`. -/
theorem equiv_cartanAction_apply (x : H) (v : RankOneModule R hA lam n hlam) :
    equiv R hA lam n hlam (cartanAction R (RankOneModule R hA lam n hlam) x v) =
      (lam x - (n : K) * 2⁻¹ * R.root default x) • equiv R hA lam n hlam v +
        (2⁻¹ * R.root default x) • Sl2Std.diag K n (equiv R hA lam n hlam v) := by
  rw [cartanAction_eq]
  simp [LinearEquiv.conjAlgEquiv_apply]

/-- Transporting the Cartan action of the simple coroot `R.coroot i` on
`RankOneModule R hA lam n hlam` across `equiv` yields `Sl2Std.diag K n`. -/
@[simp]
theorem equiv_cartanAction_coroot_apply (i : I) (v : RankOneModule R hA lam n hlam) :
    equiv R hA lam n hlam (cartanAction R (RankOneModule R hA lam n hlam) (R.coroot i) v) =
      Sl2Std.diag K n (equiv R hA lam n hlam v) := by
  rw [cartanAction_coroot]
  simp [LinearEquiv.conjAlgEquiv_apply]

/-- Coordinate basis vector `vₖ` has weight `lam - k • αᵢ`. -/
theorem basis_mem_weightSpace (i : I) (k : Fin (n + 1)) :
    basis R hA lam n hlam k ∈
      weightSpace R (RankOneModule R hA lam n hlam) (lam - (k : ℕ) • R.root i) := by
  rw [Unique.eq_default i, mem_weightSpace_iff]
  intro x
  apply (equiv R hA lam n hlam).injective
  rw [equiv_cartanAction_apply, map_smul, equiv_basis, Sl2Std.diag_basis]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_smul, ← add_smul, nsmul_eq_mul]
  congr 1
  have h2 : (2⁻¹ : K) * 2 = 1 := inv_mul_cancel₀ two_ne_zero
  linear_combination ((n : K) * R.root default x - 2 * (k : K) * R.root default x) * h2

include hA in
private theorem sub_nsmul_root_injective (i : I) :
    Function.Injective (fun k : Fin (n + 1) ↦ lam - (k : ℕ) • R.root i) := by
  rw [Unique.eq_default i]
  intro k₁ k₂ hk
  have hsub : (k₁ : ℕ) • R.root default = (k₂ : ℕ) • R.root default := sub_right_inj.mp hk
  have hev := congrArg (fun φ : Dual K H ↦ φ (R.coroot default)) hsub
  simp only [LinearMap.smul_apply, R.root_coroot_eq_two hA, nsmul_eq_mul] at hev
  exact Fin.ext (Nat.cast_injective (mul_right_cancel₀ (two_ne_zero (α := K)) hev))

/-- Each weight space `lam - k • αᵢ` of `RankOneModule` is the line spanned by `basis k`. -/
theorem weightSpace_sub_nsmul_root (i : I) (k : Fin (n + 1)) :
    weightSpace R (RankOneModule R hA lam n hlam) (lam - (k : ℕ) • R.root i) =
      K ∙ basis R hA lam n hlam k :=
  weightSpace_eq_of_iSup_eq_top R (RankOneModule R hA lam n hlam)
    (W := fun j : Fin (n + 1) ↦ K ∙ basis R hA lam n hlam j)
    (w := fun j : Fin (n + 1) ↦ lam - (j : ℕ) • R.root i)
    (fun j ↦ (Submodule.span_singleton_le_iff_mem _ _).mpr
      (basis_mem_weightSpace R hA lam n hlam i j))
    (basis R hA lam n hlam).iSup_span_singleton_eq_top (sub_nsmul_root_injective R hA lam n i) k

/-- Every weight space `lam - k • αᵢ` of `RankOneModule` is one-dimensional. -/
@[simp]
theorem finrank_weightSpace_sub_nsmul_root (i : I) (k : Fin (n + 1)) :
    Module.finrank K
        (weightSpace R (RankOneModule R hA lam n hlam) (lam - (k : ℕ) • R.root i)) = 1 := by
  rw [weightSpace_sub_nsmul_root]
  exact finrank_span_singleton ((basis R hA lam n hlam).ne_zero k)

/-- Every weight space of `RankOneModule` at a weight not of the form `lam - k • αᵢ`
(`k : Fin (n + 1)`) is trivial (`⊥`). -/
theorem weightSpace_eq_bot_of_forall_ne {i : I} {μ : Dual K H}
    (hμ : ∀ k : Fin (n + 1), μ ≠ lam - (k : ℕ) • R.root i) :
    weightSpace R (RankOneModule R hA lam n hlam) μ = ⊥ :=
  weightSpace_eq_bot_of_iSup_eq_top R (RankOneModule R hA lam n hlam)
    (W := fun j : Fin (n + 1) ↦ K ∙ basis R hA lam n hlam j)
    (w := fun j : Fin (n + 1) ↦ lam - (j : ℕ) • R.root i)
    (fun j ↦ (Submodule.span_singleton_le_iff_mem _ _).mpr
      (basis_mem_weightSpace R hA lam n hlam i j))
    (basis R hA lam n hlam).iSup_span_singleton_eq_top fun ⟨k, hk⟩ ↦ hμ k hk.symm

/-- **`RankOneModule R hA lam n hlam` is a simple `Enveloping R`-module.** -/
instance isSimpleModule :
    IsSimpleModule (Enveloping R) (RankOneModule R hA lam n hlam) where
  eq_bot_or_eq_top P := by
    by_cases hP : P = ⊥
    · exact Or.inl hP
    · refine Or.inr (Submodule.eq_top_iff'.mpr fun v ↦ ?_)
      let e := equiv R hA lam n hlam
      set Q : Submodule K (Sl2Std K n) := (P.restrictScalars K).map e.toLinearMap
      have hQ_ne : Q ≠ ⊥ := by
        obtain ⟨x, hxP, hx0⟩ := (Submodule.ne_bot_iff P).mp hP
        exact (Submodule.ne_bot_iff Q).mpr
          ⟨e x, Submodule.mem_map_of_mem hxP, (map_ne_zero_iff e e.injective).mpr hx0⟩
      have hQ_top : Q = ⊤ := Sl2Std.eq_top_of_raise_mem_of_lower_mem Q hQ_ne
        (fun _ hw ↦ by
          rcases hw with ⟨x, hx, rfl⟩
          exact ⟨positiveAction R _ default x,
            by rw [positiveAction_apply]; exact P.smul_mem _ hx, equiv_positiveAction_apply ..⟩)
        (fun _ hw ↦ by
          rcases hw with ⟨x, hx, rfl⟩
          exact ⟨negativeAction R _ default x,
            by rw [negativeAction_apply]; exact P.smul_mem _ hx, equiv_negativeAction_apply ..⟩)
      have hvQ : e v ∈ Q := hQ_top ▸ Submodule.mem_top
      obtain ⟨x, hxP, hxe⟩ := hvQ
      exact e.injective hxe ▸ hxP

/-- **`RankOneModule R hA lam n hlam` lies in `IsIntegrableO R`.** -/
theorem isIntegrableO : IsIntegrableO R (RankOneModule R hA lam n hlam) where
  isWeightModule := by
    rw [isWeightModule_iff, ← top_le_iff, ← (basis R hA lam n hlam).span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact le_iSup (weightSpace R (RankOneModule R hA lam n hlam))
      (lam - (k : ℕ) • R.root default) (basis_mem_weightSpace R hA lam n hlam default k)
  finiteDimensional_weightSpace _ := inferInstance
  exists_finset_rootLE := ⟨{lam}, fun μ hμ ↦ ⟨lam, Finset.mem_singleton_self lam, by
    by_contra hle
    refine hμ (weightSpace_eq_bot_of_forall_ne R hA lam n hlam (i := default) fun k hk ↦ hle ?_)
    rw [hk, CartanRealization.rootLE_iff, sub_sub_cancel]
    exact nsmul_mem (R.root_mem_posRootCone default) k⟩⟩
  locallyNilpotent_positiveAction i :=
    (isNilpotent_positiveAction R hA lam n hlam i).exists_pow_apply_eq_zero
  locallyNilpotent_negativeAction i :=
    (isNilpotent_negativeAction R hA lam n hlam i).exists_pow_apply_eq_zero

/-- On `RankOneModule R hA lam n hlam`, `simpleWeylIntertwiner` corresponds under `equiv` to
`TauCeti.Sl2Std.weylUnit K n`. -/
@[simp]
theorem equiv_simpleWeylIntertwiner_apply {i : I}
    (he : ∀ m : RankOneModule R hA lam n hlam,
      ∃ k : ℕ, (positiveAction R (RankOneModule R hA lam n hlam) i ^ k) m = 0)
    (hf : ∀ m : RankOneModule R hA lam n hlam,
      ∃ k : ℕ, (negativeAction R (RankOneModule R hA lam n hlam) i ^ k) m = 0)
    (v : RankOneModule R hA lam n hlam) :
    equiv R hA lam n hlam (simpleWeylIntertwiner he hf v) =
      (Sl2Std.weylUnit K n : Module.End K (Sl2Std K n)) (equiv R hA lam n hlam v) := by
  let : Module ℚ (RankOneModule R hA lam n hlam) := Module.compHom _ (algebraMap ℚ K)
  let φ := (equiv R hA lam n hlam).symm.conjAlgEquiv K
  have hep : (Module.End.locallyNilpotentExp
      (positiveAction R (RankOneModule R hA lam n hlam) i) he).toLinearMap =
      φ (IsNilpotent.exp (Sl2Std.raise K n)) := by
    rw [Module.End.locallyNilpotentExp_eq_exp _ (isNilpotent_positiveAction R hA lam n hlam i),
      positiveAction_eq, IsNilpotent.map_exp Sl2Std.isNilpotent_raise φ]
  have hfn : (Module.End.locallyNilpotentExp
      (-negativeAction R (RankOneModule R hA lam n hlam) i)
      (fun x ↦ by
        simpa [Module.End.neg_pow_apply_eq_zero_iff] using hf x)).toLinearMap =
      φ (IsNilpotent.exp (-(Sl2Std.lower K n))) := by
    rw [Module.End.locallyNilpotentExp_eq_exp _ (isNilpotent_negativeAction R hA lam n hlam i).neg,
      negativeAction_eq, ← map_neg, IsNilpotent.map_exp Sl2Std.isNilpotent_lower.neg φ]
  have hweyl : (simpleWeylIntertwiner he hf).toLinearMap =
      φ (Sl2Std.weylUnit K n : Module.End K (Sl2Std K n)) := by
    ext x
    rw [LinearEquiv.coe_coe, simpleWeylIntertwiner_apply, Sl2Std.coe_weylUnit, map_mul, map_mul,
      _root_.mul_apply_eq_comp, _root_.mul_apply_eq_comp, ← LinearEquiv.coe_toLinearMap, hep,
      ← LinearEquiv.coe_toLinearMap, hfn]
  have hv := congrArg (fun g : Module.End K (RankOneModule R hA lam n hlam) ↦
    equiv R hA lam n hlam (g v)) hweyl
  simpa [φ, LinearEquiv.conjAlgEquiv_apply] using hv

/-- On the coordinate basis of `RankOneModule`, `simpleWeylIntertwiner` reverses the basis with
signs `(-1) ^ (n - k)`. -/
@[simp]
theorem simpleWeylIntertwiner_basis {i : I}
    (he : ∀ m : RankOneModule R hA lam n hlam,
      ∃ k : ℕ, (positiveAction R (RankOneModule R hA lam n hlam) i ^ k) m = 0)
    (hf : ∀ m : RankOneModule R hA lam n hlam,
      ∃ k : ℕ, (negativeAction R (RankOneModule R hA lam n hlam) i ^ k) m = 0)
    (k : Fin (n + 1)) :
    simpleWeylIntertwiner he hf (basis R hA lam n hlam k) =
      ((-1 : K) ^ (n - (k : ℕ))) • basis R hA lam n hlam k.rev := by
  apply (equiv R hA lam n hlam).injective
  rw [equiv_simpleWeylIntertwiner_apply, equiv_basis, map_smul, equiv_basis,
    Sl2Std.weylUnit_apply_basis]

/-- **Squaring `simpleWeylIntertwiner` on `RankOneModule`.** Two applications of the simple Weyl
intertwiner multiply every vector of `RankOneModule R hA lam n hlam` by `(-1) ^ n` (so on `n = 1`
it acts as `-1`, not `+1`, whereas on `n = 2` it acts as `+1`). -/
@[simp]
theorem simpleWeylIntertwiner_simpleWeylIntertwiner_apply {i : I}
    (he : ∀ m : RankOneModule R hA lam n hlam,
      ∃ k : ℕ, (positiveAction R (RankOneModule R hA lam n hlam) i ^ k) m = 0)
    (hf : ∀ m : RankOneModule R hA lam n hlam,
      ∃ k : ℕ, (negativeAction R (RankOneModule R hA lam n hlam) i ^ k) m = 0)
    (v : RankOneModule R hA lam n hlam) :
    simpleWeylIntertwiner he hf (simpleWeylIntertwiner he hf v) = (-1 : K) ^ n • v := by
  apply (equiv R hA lam n hlam).injective
  rw [equiv_simpleWeylIntertwiner_apply, equiv_simpleWeylIntertwiner_apply, map_smul,
    Sl2Std.weylUnit_weylUnit_apply]

end CharZero

end RankOneModule

end RankOneModule

end KacMoody

end TauCeti
