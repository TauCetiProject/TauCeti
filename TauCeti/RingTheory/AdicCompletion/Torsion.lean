/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import TauCeti.RingTheory.AdicCompletion.AlgHom

/-!
# The completion action on ideal-power-torsion modules

An `R`-module in which every element is killed by a power of `I` has a canonical action of
`AdicCompletion I R`. On an element killed by `I ^ n`, a completed scalar acts through its
residue modulo `I ^ n`. The hypothesis is membership of every element in
`Ideal.primaryComponent M I`. No finite generation or Noetherian hypothesis is needed.

`TauCeti.AdicCompletion.torsionModule` constructs this module structure. The residue formula
`AdicCompletion.torsionModule_smul_eq` characterizes its action. Every `R`-linear map
between such modules is linear for these completion actions, and restriction of scalars recovers
the original action of `R`.

The construction uses the compatible residues of Mathlib's `AdicCompletion`, formalized by
Judith Ludwig and Christian Merten, and the quotient actions on `Submodule.torsionBySet`.
For its role in Matlis duality, see the Stacks Project,
Section 47.7, Tag 08Z1.
-/

public section

noncomputable section

namespace AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

private def torsionActionAt (a : AdicCompletion I R) {n : ℕ} {x : M}
    (hx : x ∈ Submodule.torsionBySet R M ↑(I ^ n)) : M :=
  ↑(evalₐ I n a • (⟨x, hx⟩ : Submodule.torsionBySet R M ↑(I ^ n)))

private theorem torsionActionAt_eq {a : AdicCompletion I R} {x : M} {n : ℕ} {r : R}
    (hx : x ∈ Submodule.torsionBySet R M ↑(I ^ n))
    (ha : evalₐ I n a = Ideal.Quotient.mk (I ^ n) r) :
    torsionActionAt a hx = r • x := by
  simp only [torsionActionAt, ha, Submodule.torsionBySet.mk_smul, Submodule.coe_smul_of_tower]

private theorem torsionActionAt_mono (a : AdicCompletion I R) {x : M} {n m : ℕ}
    (h : n ≤ m) (hx : x ∈ Submodule.torsionBySet R M ↑(I ^ n))
    (hy : x ∈ Submodule.torsionBySet R M ↑(I ^ m)) :
    torsionActionAt a hx = torsionActionAt a hy := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I m a)
  have hn : evalₐ I n a = Ideal.Quotient.mk (I ^ n) r := by
    rw [← factor_evalₐ h a, ← hr, Ideal.Quotient.factor_mk]
  rw [torsionActionAt_eq hx hn, torsionActionAt_eq hy hr.symm]

variable (hM : ∀ x : M, x ∈ Ideal.primaryComponent M I)

private def torsionAction (a : AdicCompletion I R) (x : M) : M :=
  torsionActionAt a ((Ideal.primaryComponent_mem M I x).mp (hM x)).choose_spec

private theorem torsionAction_eq (a : AdicCompletion I R) {x : M} {n : ℕ}
    (hx : x ∈ Submodule.torsionBySet R M ↑(I ^ n)) :
    torsionAction hM a x = torsionActionAt a hx := by
  let h := (Ideal.primaryComponent_mem M I x).mp (hM x)
  let k := max n h.choose
  have hk : x ∈ Submodule.torsionBySet R M ↑(I ^ k) :=
    Submodule.torsionBySet_le_torsionBySet_pow _ _ (Nat.le_max_left _ _) I hx
  have hchosen : x ∈ Submodule.torsionBySet R M ↑(I ^ h.choose) := h.choose_spec
  exact (torsionActionAt_mono a (Nat.le_max_right _ _) hchosen hk).trans
    (torsionActionAt_mono a (Nat.le_max_left _ _) hx hk).symm

end AdicCompletion

namespace TauCeti.AdicCompletion

open _root_.AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (hM : ∀ x : M, x ∈ Ideal.primaryComponent M I)

/-- The canonical module structure over the completion on a module whose elements are each
annihilated by a power of `I`. Use it with `letI := TauCeti.AdicCompletion.torsionModule hM`. -/
@[instance_reducible]
def torsionModule : Module (AdicCompletion I R) M where
  smul := torsionAction hM
  one_smul x := by
    -- The structure field uses the scalar operation being constructed.
    change torsionAction hM 1 x = x
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I x).mp (hM x)
    rw [torsionAction_eq hM 1 hn]
    simp [torsionActionAt]
  mul_smul a b x := by
    -- Expand the scalar operation of this structure before applying its residue formula.
    change torsionAction hM (a * b) x = torsionAction hM a (torsionAction hM b x)
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I x).mp (hM x)
    have hb : torsionAction hM b x ∈ Submodule.torsionBySet R M ↑(I ^ n) := by
      rw [torsionAction_eq hM b hn]
      exact (evalₐ I n b • (⟨x, hn⟩ : Submodule.torsionBySet R M ↑(I ^ n))).property
    rw [torsionAction_eq hM (a * b) hn, torsionAction_eq hM a hb]
    have hinner : (⟨torsionAction hM b x, hb⟩ : Submodule.torsionBySet R M ↑(I ^ n)) =
        evalₐ I n b • (⟨x, hn⟩ : Submodule.torsionBySet R M ↑(I ^ n)) :=
      Subtype.ext (torsionAction_eq hM b hn)
    simp only [torsionActionAt, map_mul, mul_smul, hinner]
  smul_zero a := by
    -- The scalar operation is the action defined above.
    change torsionAction hM a 0 = 0
    rw [torsionAction_eq hM a (Submodule.zero_mem (Submodule.torsionBySet R M ↑(I ^ 0)))]
    exact congrArg Subtype.val (smul_zero (evalₐ I 0 a) :
      evalₐ I 0 a • (0 : Submodule.torsionBySet R M ↑(I ^ 0)) = 0)
  smul_add a x y := by
    -- Expand the scalar operation of this structure before applying its residue formula.
    change torsionAction hM a (x + y) = torsionAction hM a x + torsionAction hM a y
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I x).mp (hM x)
    obtain ⟨m, hm⟩ := (Ideal.primaryComponent_mem M I y).mp (hM y)
    have hx : x ∈ Submodule.torsionBySet R M ↑(I ^ (max n m)) :=
      Submodule.torsionBySet_le_torsionBySet_pow _ _ (Nat.le_max_left _ _) I hn
    have hy : y ∈ Submodule.torsionBySet R M ↑(I ^ (max n m)) :=
      Submodule.torsionBySet_le_torsionBySet_pow _ _ (Nat.le_max_right _ _) I hm
    rw [torsionAction_eq hM a (Submodule.add_mem _ hx hy), torsionAction_eq hM a hx,
      torsionAction_eq hM a hy]
    exact congrArg Subtype.val (smul_add (evalₐ I (max n m) a)
      (⟨x, hx⟩ : Submodule.torsionBySet R M ↑(I ^ (max n m))) ⟨y, hy⟩)
  add_smul a b x := by
    -- Expand the scalar operation of this structure before applying its residue formula.
    change torsionAction hM (a + b) x = torsionAction hM a x + torsionAction hM b x
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I x).mp (hM x)
    rw [torsionAction_eq hM (a + b) hn, torsionAction_eq hM a hn, torsionAction_eq hM b hn]
    simp [torsionActionAt, add_smul]
  zero_smul x := by
    -- The structure field uses the scalar operation being constructed.
    change torsionAction hM 0 x = 0
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I x).mp (hM x)
    rw [torsionAction_eq hM 0 hn]
    simp [torsionActionAt]

end TauCeti.AdicCompletion

namespace AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (hM : ∀ x : M, x ∈ Ideal.primaryComponent M I)

/-- A completed scalar acts on an element killed by `I ^ n` through its residue modulo
`I ^ n`. This formula permits any representative of the residue. -/
theorem torsionModule_smul_eq (a : AdicCompletion I R) (x : M) {n : ℕ} (r : R)
    (hx : x ∈ Submodule.torsionBySet R M ↑(I ^ n))
    (ha : evalₐ I n a = Ideal.Quotient.mk (I ^ n) r) :
    letI := TauCeti.AdicCompletion.torsionModule hM
    a • x = r • x := by
  exact (torsionAction_eq hM a hx).trans (torsionActionAt_eq hx ha)

end AdicCompletion

namespace TauCeti.AdicCompletion

open _root_.AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (hM : ∀ x : M, x ∈ Ideal.primaryComponent M I)

/-- The canonical completion action extends the scalar tower from `R`. -/
instance torsionModule_isScalarTower :
    letI := torsionModule hM
    IsScalarTower R (AdicCompletion I R) M := by
  let := torsionModule hM
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I x).mp (hM x)
  exact torsionModule_smul_eq hM _ x r hn (evalₐ_of I n r)

end TauCeti.AdicCompletion

namespace LinearMap

variable {R : Type*} [CommRing R] {I : Ideal R}
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (hM : ∀ x : M, x ∈ Ideal.primaryComponent M I)
variable (hN : ∀ y : N, y ∈ Ideal.primaryComponent N I)

/-- An `R`-linear map between ideal-power-torsion modules commutes with the canonical
completion actions. -/
@[simp]
theorem map_adicCompletion_smul (f : M →ₗ[R] N) (a : AdicCompletion I R) (x : M) :
    letI := TauCeti.AdicCompletion.torsionModule hM
    letI := TauCeti.AdicCompletion.torsionModule hN
    f (a • x) = a • f x := by
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I x).mp (hM x)
  have hfx : f x ∈ Submodule.torsionBySet R N ↑(I ^ n) := by
    rw [Submodule.mem_torsionBySet_iff] at hn ⊢
    intro r
    rw [← f.map_smul, hn r, f.map_zero]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n a)
  rw [AdicCompletion.torsionModule_smul_eq hM a x r hn hr.symm,
    AdicCompletion.torsionModule_smul_eq hN a (f x) r hfx hr.symm, f.map_smul]

end LinearMap

namespace TauCeti.AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (hM : ∀ x : M, x ∈ Ideal.primaryComponent M I)
variable (hN : ∀ y : N, y ∈ Ideal.primaryComponent N I)

/-- Restriction of scalars identifies linear maps for the canonical completion actions with
`R`-linear maps between ideal-power-torsion modules. -/
def torsionRestrictScalarsEquiv :
    letI := TauCeti.AdicCompletion.torsionModule hM
    letI := TauCeti.AdicCompletion.torsionModule hN
    (M →ₗ[AdicCompletion I R] N) ≃ₗ[R] (M →ₗ[R] N) := by
  letI := TauCeti.AdicCompletion.torsionModule hM
  letI := TauCeti.AdicCompletion.torsionModule hN
  exact
    { LinearMap.restrictScalarsₗ R (AdicCompletion I R) M N R with
      invFun := fun f ↦
        { toFun := f
          map_add' := f.map_add
          map_smul' := f.map_adicCompletion_smul hM hN }
      left_inv := fun f ↦ by ext; rfl
      right_inv := fun f ↦ by ext; rfl }

/-- The comparison of Hom modules is restriction of scalars. -/
@[simp]
theorem torsionRestrictScalarsEquiv_apply
    (f : letI := TauCeti.AdicCompletion.torsionModule hM
         letI := TauCeti.AdicCompletion.torsionModule hN
         M →ₗ[AdicCompletion I R] N) (x : M) :
    torsionRestrictScalarsEquiv hM hN f x = f x := (rfl)

/-- Extending a linear map to the canonical completion actions preserves its values. -/
@[simp]
theorem torsionRestrictScalarsEquiv_symm_apply (f : M →ₗ[R] N) (x : M) :
    (torsionRestrictScalarsEquiv hM hN).symm f x = f x := (rfl)

end TauCeti.AdicCompletion
